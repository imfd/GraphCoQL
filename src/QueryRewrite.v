
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

  Variables N Name Vals : ordType.
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
  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.

  Open Scope fset.

  Equations normalize schema : @NamedType Name -> @Query Name Vals -> seq (@Query Name Vals) :=
    {
      normalize _ type_in_scope (SingleField f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: SingleField f α];
        | _ := let possible_types := get_possible_types schema type_in_scope in
              (fun ty => InlineFragment ty [:: SingleField f α]) @: possible_types
        };

       normalize schema  type_in_scope (LabeledField l f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: LabeledField l f α];
        | _ := let possible_types := get_possible_types schema type_in_scope in
              (fun ty => InlineFragment ty [:: (LabeledField l f α)]) @: possible_types
        };
      
                                                                                    
       normalize schema  type_in_scope (NestedField f α φ)
         with lookup_field_in_type schema type_in_scope f :=
         {
          | Some fld
              with is_object_type schema type_in_scope :=
              {
              | true := [:: NestedField f α (normalize__φ schema fld.(return_type) φ)];
              | _ :=
                let possible_types := get_possible_types schema type_in_scope in
                let normalized_head := normalize__φ schema fld.(return_type) φ in
                 (fun ty => InlineFragment ty [:: NestedField f α normalized_head]) @: possible_types
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
              | _ :=
                let possible_types := get_possible_types schema type_in_scope in
                let normalized_head := normalize__φ schema fld.(return_type) φ in
                (fun ty => InlineFragment ty [:: NestedLabeledField l f α normalized_head]) @: possible_types
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
      move: Hqc; query_conforms; move=> [_ _ _ Hqsc].
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
  
  Lemma normalize__φ_in_abstract_scope_are_inlines :
    forall schema ty qs,
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      is_abstract_type schema ty ->
      all is_inline_fragment (normalize__φ schema ty qs).
  Proof.
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
    
  Qed.

   Lemma normalize_in_abstract_scope_are_inlines :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      is_abstract_type schema ty ->
      all is_inline_fragment (normalize schema ty q).
  Proof.
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


  
  Lemma imfset_inline_are_grounded_in_interface schema ty sbq :
    is_interface_type schema ty ->
    all is_field sbq ->
    all (is_grounded_2 schema ty) sbq -> 
    all (is_grounded_2 schema ty) ((fun t => InlineFragment t sbq) @: (get_possible_types schema ty)).
  Proof.
    move=> Hintf Hflds Hg.
    move: (@in_possible_types_is_object Name Vals schema ty).
    rewrite get_possible_types_interfaceE //.
    
    elim/fset_ind: (implementation schema ty); [by rewrite imfset0| move=> x tl Hnin IH Hinobj].
    rewrite imfsetU all_fsetU; apply_andP.
    - rewrite imfset1 /=; apply_andP.
      simp is_grounded_2; apply_and3P.
      by have/Hinobj: x \in x |: tl by rewrite in_fsetU1; orL.
  Abort.
      
      
      
      

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
      apply: imfset_inline_are_inlines.
      move: (@in_possible_types_is_object Name Vals schema s).
      rewrite get_possible_types_interfaceE //.
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

  Admitted.
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
      move: (type_in_scope_N_obj_is_abstract Hqc Hobj) => Habs.
      move: (normalize_in_abstract_scope_are_inlines _ _ _ Hqc Hv Habs) => Hinline.
      move: (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hqsc Hvs Habs) => Hinlines.
        by orR; apply/andP.
   Qed.
    

   Equations  β__subqueryextract : @Query Name Vals -> @Query Name Vals -> seq (@Query Name Vals) :=
        {
          β__subqueryextract (NestedField f α β) (NestedField f' α' χ)
            with f == f', α == α' :=
            {
            | true | true := χ;
            | _ | _ := [::]
            };
          
          β__subqueryextract (NestedLabeledField l f α β) (NestedLabeledField l' f' α' χ)
            with [&& l == l', (f == f') & (α == α')] :=
            {
            | true := χ;
            | _ := [::]
            };
          
          β__subqueryextract (InlineFragment t β) (InlineFragment t' χ)
            with (t == t') :=
            {
            | true => χ;
            | false => [::]
            };
          
          β__subqueryextract _ _ := [::]
        }.
   
   Fixpoint β__φ (flt : @Query Name Vals) queries : seq Query :=
     match queries with
     | [::] => [::]
     | hd :: tl =>  (β__subqueryextract flt hd) ++ (β__φ flt tl)
     end.

  Lemma β__subqueryextract_size_reduced flt q :
    queries_size (β__subqueryextract flt q) < query_size q.
  Proof.
    by apply_funelim (β__subqueryextract flt q) => //=; intros; case: q0; intros; simp query_size.
  Qed.
  
  Lemma β__φ_size_reduced flt queries :
    queries_size (β__φ flt queries) <= queries_size queries.
  Proof.
    elim: queries => //= hd tl IH.
    rewrite queries_size_app.
    move: (β__subqueryextract_size_reduced flt hd) => Hlt.
    by ssromega.
  Qed.

  
  Lemma cat2s {T : Type} (x y : T) (s : seq T) :
    [:: x] ++ (y :: s) = [:: x, y & s].
  Proof. by case: s. Qed.
  
  Lemma β__φ_cons q qs x : 
    β__φ q (x :: qs) = (β__φ q [:: x]) ++ (β__φ q qs).
  Proof.
    elim: qs x => //.
      by move=> x; simp β__φ; rewrite ! cats0.
    move=> hd tl IH x /=.
    by rewrite cats0.
  Qed.

      
  Lemma β__φ_cat q qs qs' :
    β__φ q (qs ++ qs') = (β__φ q qs) ++ (β__φ q qs').
  Proof.
    elim: qs qs' => // hd tl IH qs'.    
    rewrite cat_cons.
    rewrite β__φ_cons [β__φ q (hd :: tl)]β__φ_cons.
    by rewrite (IH qs') catA.
  Qed.
  
  Definition γ__φ (flt : Query) (queries : seq Query) : seq (@Query Name Vals) :=
    [seq query <- queries | ~~ partial_query_eq flt query].


  Lemma γ__φ_no_repetition flt queries :
    forall q, q \in (γ__φ flt queries) ->
               partial_query_eq flt q = false.
  Proof.
    move=> q.
    rewrite /γ__φ mem_filter => /andP [H _].
    by move: H; rewrite /negb; case: ifP.
  Qed.

    
    
  Obligation Tactic := intros; simp query_size; do ? ssromega; rewrite ?queries_size_app.  
  Equations remove_redundancies (queries : seq (@Query Name Vals)) : seq (@Query Name Vals)
    by wf (queries_size queries) lt :=
    {
      remove_redundancies [::] := [::];
      
      remove_redundancies ((SingleField f α) :: queries) :=
        let filtered := remove_redundancies queries in
        (SingleField f α) :: (γ__φ (SingleField f α) filtered);
      
      remove_redundancies ((LabeledField l f α) :: queries) :=
        let filtered := remove_redundancies queries in
        (LabeledField l f α) :: (γ__φ (LabeledField l f α) filtered);

      remove_redundancies ((NestedField f α φ) :: queries) :=
        let filtered := remove_redundancies queries in
        (NestedField f α (remove_redundancies (φ ++ (β__φ (NestedField f α φ) queries)))) :: (γ__φ (NestedField f α φ) filtered);

      remove_redundancies ((NestedLabeledField l f α φ) :: queries) :=
        let filtered := remove_redundancies queries in
        (NestedLabeledField l f α (remove_redundancies (φ ++ (β__φ (NestedLabeledField l f α φ) queries)))) :: (γ__φ (NestedLabeledField l f α φ) filtered);

      remove_redundancies ((InlineFragment t φ) :: queries) :=
        let filtered := remove_redundancies queries in
        (InlineFragment t (remove_redundancies (φ ++ (β__φ (InlineFragment t φ) queries)))) :: (γ__φ (InlineFragment t φ) filtered)
      
    }.
  Next Obligation.
    by move: (β__φ_size_reduced (NestedField f α φ) queries) => Hlt; ssromega.
  Qed.
  Next Obligation.
     by move: (β__φ_size_reduced (NestedLabeledField l f α φ) queries) => Hlt; ssromega.
  Qed.
  Next Obligation.
    by move: (β__φ_size_reduced (InlineFragment t φ) queries) => Hlt; ssromega.
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


  Lemma filter_preserves_non_redundancy flt queries :
    are_non_redundant queries ->
    are_non_redundant (γ__φ flt queries).
  Proof.
    elim: queries => // hd tl IH.
    rewrite are_non_redundant_equation_2.
    case Hhas: has => //=.
    move/andP=> [Hnr Hnrtl].
    case: ifP => //; last first.
      by move=> _; apply: IH.
    rewrite are_non_redundant_equation_2.
    case Hhas': has => //=.  
    move/negbT: Hhas => /hasPn Hhas.
    move/hasP: Hhas' => [q].
    rewrite mem_filter => /andP [Hneq Hin].
    by move: (Hhas q Hin) => /negbTE ->.
    by move=> _; apply/andP; split => //; apply IH.
  Qed.


      
  Lemma remove_redundancies_is_non_redundant queries :
    are_non_redundant (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //;
    rewrite are_non_redundant_equation_2;
    case Hhas: has => //=.

    all: do ?[by move/hasP: Hhas => [q Hin];
              move: (γ__φ_no_repetition _ _ q Hin) ->].

    all: do ?[by apply/andP; split => //=;
              apply (filter_preserves_non_redundancy _ _ H)].
    all:  move/hasP: Hhas => [q Hin];
          move: (γ__φ_no_repetition _ _ q Hin);
          rewrite /partial_query_eq; case: q Hin => //=.
    - by move=> f' α' χ Hin ->.
    - by move=> l' f' α' χ Hin ->.
    - by move=> t' χ Hin ->.
  Qed.

  Lemma remove_redundancies_preserves_all_fields queries :
    all is_field queries ->
    all is_field (remove_redundancies queries).
  Proof.
    elim: queries => //= hd tl IH.
    by case: hd => //=;
    intros; move/andP: H => [Hf Hfs]; simp remove_redundancies => /=;
    apply/andP; split=> //; apply: filter_preserves_pred; apply: IH.
  Qed.

  Lemma remove_redundancies_preserves_all_inlines queries :
    all is_inline_fragment queries ->
    all is_inline_fragment (remove_redundancies queries).
  Proof.
    elim: queries => //= hd tl IH.
    by case: hd => //=;
    intros; move/andP: H => [Hin Hins]; simp remove_redundancies => /=;
    apply/andP; split=> //; apply: filter_preserves_pred; apply: IH.
  Qed.
  


  Lemma notin_in_false {T : eqType} (x : T) (xs : mem_pred T) :
    x \notin xs -> x \in xs = false.
  Proof.
      by rewrite /negb; case: ifP.
  Qed.

 

  Lemma γ__φ_no_repetition_eq q qs :
    (forall x, x \in qs -> ~~partial_query_eq q x) ->
               γ__φ q qs = qs.
  Proof.
    elim: qs => //= hd tl IH H.
    case: ifP => Hf.
    congr cons.
    by apply: IH => x Hin; apply: H; apply: mem_tail.
    have: hd \in hd :: tl by apply: mem_head.
    by move/H; rewrite Hf.
  Qed.
  
  Lemma remove_redundancies_uniq q qs :
    ~~ has (partial_query_eq q) qs ->
    remove_redundancies (q :: qs) = [seq (remove_redundancies__φ q') | q' <- q :: qs].
  Proof.
    move/hasPn.
    case: q => //.
    - move=> f α H; simp remove_redundancies => /=; simp remove_redundancies__φ; congr cons.
      rewrite (γ__φ_no_repetition_eq _ (remove_redundancies qs)).
  Abort.


  (*
  Lemma remove_redundancies_inlined_query schema type_in_scope q :
    remove_redundancies [seq (InlineFragment ty [:: q]) | ty <- get_possible_types schema type_in_scope] =
    [seq (InlineFragment ty (remove_redundancies [:: q])) | ty <- get_possible_types schema type_in_scope].
  Proof.
    apply_funelim (get_possible_types schema type_in_scope) => //=.
    - move=> ty o intfs flds /lookup_type_name_wf /= ->.
      simp remove_redundancies => /=.
        by simp β__φ => /=; simp remove_redundancies.
    - move=> ty i flds Hlook.
      elim/fset_ind: (implementation schema i) => //= x xs Hnin IH.
      
  Admitted.
*)

  Lemma remove_redundancies_inlined_query schema type_in_scope q :
    remove_redundancies ((fun ty => InlineFragment ty [:: q]) @: (get_possible_types schema type_in_scope)) =
    ((fun ty => InlineFragment ty (remove_redundancies [:: q])) @: (get_possible_types schema type_in_scope)).
  Proof.
      
  Admitted.

    
    
 



  (*
  Ltac contr_scope_type s ty :=
    match goal with
    | [ H : is_object_type s ty, Hcontr : is_object_type s ty = false |- _ ] => rewrite H in Hcontr; inversion Hcontr
    end.
   *)

  Lemma γ__φ_non_redundant_eq q qs :
    are_non_redundant (q :: qs) ->
    γ__φ q qs = qs.
  Proof.
    rewrite are_non_redundant_equation_2.
    case Hhas: has => //= _.
    move/hasPn: Hhas => /allP /all_filterP Heq.
      by rewrite /γ__φ Heq.
  Qed.

  Lemma β__subqueryextract_not_eq_nil q1 q2 :
    ~~partial_query_eq q1 q2 ->
    β__subqueryextract q1 q2 = [::].
  Proof.
    apply_funelim (β__subqueryextract q1 q2) => //=.
    - move=> α α' f f' φ χ /eqP Hα /eqP Hf /nandP.
        by case=> [/eqP Hnf | /eqP Hnα]; [rewrite Hf in Hnf | rewrite Hα in Hnα].
    - by move=> l f α l' f' α' φ χ /and3P [/eqP Hl /eqP Hf /eqP Hα]
              /nandP [/eqP Hnl | /nandP [ /eqP Hnf | /eqP Hnα]];
     [rewrite Hl in Hnl | rewrite Hf in Hnf | rewrite Hα in Hnα].
    - by move=> t t' α χ /eqP -> /eqP.
  Qed.
  
  Lemma β__φ_has_none_nil flt queries :
    has (partial_query_eq flt) queries = false ->
    β__φ flt queries = [::].
  Proof.
    elim: queries => // hd tl IH.
    move/hasPn/allP=> /= /andP [Hneq /allP/hasPn/negbTE Hntl].
    rewrite (IH Hntl) cats0.
    by apply: β__subqueryextract_not_eq_nil.
  Qed.
    
    
  Lemma non_redundant_eq_remove qs :
    are_non_redundant qs ->
    remove_redundancies qs = qs.
  Proof.
    apply_funelim (remove_redundancies qs) => // [f α | l f α | f α φ | l f α φ | t φ] χ IH.
    
    all: do ?[by intros; simp remove_redundancies => /=; congr cons;
              rewrite IH //=; [apply: γ__φ_non_redundant_eq | move: H => /=; case: has => //=]]. 

    all: do ?[move=> IH2 Hnr;
              pose Hnr' := Hnr; move: Hnr' => /=;
              case Hhas: has => //= /andP [Hhdnr Htlnr];
              rewrite IH2 => //=; rewrite β__φ_has_none_nil => //; rewrite cats0].
    all: do ?[by rewrite IH => //; congr cons; apply: γ__φ_non_redundant_eq].
    all: do [by simp is_non_redundant in Hhdnr].
  Qed.
  
      
  Definition have_same_shape qs qs' :=
    (all is_field qs /\ all is_field qs') \/
    (all is_inline_fragment qs /\ all is_inline_fragment qs').


  Lemma γ__φ_preserves_grounded schema ty flt qs :
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema ty (γ__φ flt qs).
  Proof.
    elim: qs => //= hd tl IH.
    case: ifP => // _; rewrite  ?are_grounded_2_equation_2;
    case Hobj : is_object_type => //= /and3P [Hf Hg Hgs].

    all: do ?[apply_and3P].
    all: do ?[by apply: IH].
  Qed.

 

      
  Lemma remove_redundancies_preserves_grounded_cat schema ty qs qs' :
    all (query_conforms schema ty) qs ->
    all (query_conforms schema ty) qs' ->
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema ty qs' ->
    are_non_redundant qs' ->
    are_grounded_2 schema ty (remove_redundancies (qs ++ qs')).
  Proof.
    elim: qs qs' => //=.
    - move=> qs' _ Hqsc _ Hg Hnr.
        by rewrite non_redundant_eq_remove.
        
    - move=> hd tl IH qs'.
      all_cons => [Hqc Hqsc] Hqsc' Hg Hg' Hnr.
  Abort.

  Lemma are_grounded_nil {schema ty} : are_grounded_2 schema ty [::]. Proof. done. Qed.
  Lemma are_non_redundant_nil : @are_non_redundant Name Vals [::]. Proof. done. Qed.

  Lemma β__φ_empty_for_sf f α qs :
    β__φ (SingleField f α) qs = [::].
  Proof. by elim: qs. Qed.

  Lemma β__φ_empty_for_lf l f α qs :
    β__φ (LabeledField l f α) qs = [::].
  Proof. by elim: qs. Qed.


  
  Lemma β__φ_preserves_conformance_nf schema ty f α φ fld qs :
    query_conforms schema ty (NestedField f α φ) ->
    lookup_field_in_type schema ty f = Some fld ->
    all (query_conforms schema ty) qs ->
    all (query_conforms schema (return_type fld)) (β__φ (NestedField f α φ) qs).
  Proof.
    elim: qs => // hd tl IH Hqc Hlook /=.
    case: hd => // [f' α' | l f' α' | f' α' χ | l f' α' χ | t χ] /andP [Hhdqc Hqsc];
    intros; simp β__subqueryextract; rewrite ?cat0s; do ?[apply: IH => //].

    case: eqP => //=; [case: eqP => // | by move=> _; apply: IH]; rewrite all_cat //=.
    move=> Hfeq Haeq; apply_andP.
      by move: Hhdqc; rewrite Hfeq in Hlook; rewrite {1}/query_conforms Hlook => /and4P [_ _ _].
      by apply: IH.
    by intros; apply: IH.
  Qed.

  Lemma β__φ_preserves_conformance schema q qs :
    forall ty,
    query_conforms schema ty q ->
    all (query_conforms schema ty) qs ->
    exists ty', all (query_conforms schema ty') (β__φ q qs).
  Proof.
    case: q.
    - by intros; exists ty; rewrite β__φ_empty_for_sf /=.
    - by intros; exists ty; rewrite β__φ_empty_for_lf /=.
      
    - move=> f α φ ty; rewrite {1}/query_conforms.
      case Hlook : lookup_field_in_type => [fld|] // /and4P [_ _ _ Hqsc] Hqsc'.
      exists fld.(return_type).
      elim: qs Hqsc' => // hd tl IH.
      all_cons => [Hqc Hqsc'] /=.
      case: hd Hqc => // [f' α' | l f' α' | f' α' χ | l f' α' χ | t χ] Hqc;
      intros; simp β__subqueryextract; rewrite ?cat0s; do ?[apply: IH => //].

      case: eqP => //=; [case: eqP => // | by move=> _; apply: IH]; rewrite all_cat //=.
      move=> Hfeq Haeq; apply_andP.
        by move: Hqc; rewrite Hfeq in Hlook; rewrite {1}/query_conforms Hlook => /and4P [_ _ _].
        by apply: IH.
      by intros; apply: IH.

    - move=> l f α φ ty; rewrite {1}/query_conforms.
      case Hlook : lookup_field_in_type => [fld|] // /and4P [_ _ _ Hqsc] Hqsc'.
      exists fld.(return_type).
      elim: qs Hqsc' => // hd tl IH.
      all_cons => [Hqc Hqsc'] /=.
      case: hd Hqc => // [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t χ] Hqc;
      intros; simp β__subqueryextract; rewrite ?cat0s; do ?[apply: IH => //].

      case: eqP => //=; [case: eqP => //= | by intros; apply: IH];
                    [case: eqP => //= | by intros; apply: IH];
                    [rewrite all_cat //=| by intros; apply: IH].
      move=> _ Hfeq _; apply_andP.
        by move: Hqc; rewrite Hfeq in Hlook; rewrite {1}/query_conforms Hlook => /and4P [_ _ _].
        by apply: IH.


    - move=> t φ ty; rewrite {1}/query_conforms -/(query_conforms _ _) => /and4P [_ _ _ Hqsc] Hqsc'.
      exists t.
      elim: qs Hqsc' => // hd tl IH.
      case: hd => //=; do ?[intros; move/andP: Hqsc' => [_ Hqsc']; simp β__subqueryextract; rewrite cat0s; apply: IH].

      move=> t' χ /andP [/and4P [_ _ _ Hqc] Hqsc'] /=; simp β__subqueryextract.
        by case: eqP => //=; [move=> Heq; rewrite -Heq ?all_cat in Hqc *; apply_andP; apply: IH | by intros; apply: IH].
  Qed.


  Lemma β__φ_preserves_conformance_nlf schema ty l f α φ fld qs :
    query_conforms schema ty (NestedLabeledField l f α φ) ->
    lookup_field_in_type schema ty f = Some fld ->
    all (query_conforms schema ty) qs ->
    all (query_conforms schema (return_type fld)) (β__φ (NestedLabeledField l f α φ) qs).
  Proof.
    elim: qs => // hd tl IH Hqc Hlook /=.
    case: hd => // [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t χ] /andP [Hhdqc Hqsc];
    intros; simp β__subqueryextract; rewrite ?cat0s; do ?[apply: IH => //].

    case: eqP => //=; [case: eqP => //= | by intros; apply: IH];
                    [case: eqP => //= | by intros; apply: IH];
                    [rewrite all_cat //=| by intros; apply: IH].
    move=> _ Hfeq _; apply_andP.
        by move: Hhdqc; rewrite Hfeq in Hlook; rewrite {1}/query_conforms Hlook => /and4P [_ _ _].
        by apply: IH.
  Qed. 

  Lemma β__φ_preserves_conformance_inline schema ty t φ qs :
    query_conforms schema ty (InlineFragment t φ) ->
    all (query_conforms schema ty) qs ->
    all (query_conforms schema t) (β__φ (InlineFragment t φ) qs).
  Proof.
    elim: qs => // hd tl IH Hqsc.
    all_cons => [Hqc Hqsc'].
    case: hd Hqc => //=.
    all: do ?[by intros; simp β__subqueryextract; move/andP: H => [_ H]; rewrite cat0s; apply: IH].

    move=> t' χ /and4P [_ _ _ Hqc] /=; simp β__subqueryextract.
      by case: eqP => //=; [move=> Heq; rewrite -Heq ?all_cat in Hqc *; apply_andP; apply: IH | by intros; apply: IH].
  Qed.
  
  Lemma β__φ_preserves_grounded_nf schema ty f α φ fld qs :
    query_conforms schema ty (NestedField f α φ) ->
    lookup_field_in_type schema ty f = Some fld ->
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema (return_type fld) (β__φ (NestedField f α φ) qs).
  Proof.
    elim: qs => // hd tl IH Hqc Hlook.
    case: hd => // [f' α' | l f' α' | f' α' χ | l f' α' χ | t χ] /=;
    case Hobj : is_object_type => //= /and3P [Hty Hg Hgs]; simp β__subqueryextract.

    case: eqP => //=; [case: eqP => // [Hfeq Haeq | _ _] | by move=> _; apply IH];
                  rewrite -are_grounded_2_cat //=; split=> //; do ?[by apply: IH].
    - by move: Hg; simp is_grounded_2; rewrite -Hfeq Hlook /=.
  Qed.

  
  Lemma β__φ_preserves_grounded_nlf schema ty l f α φ fld qs :
    query_conforms schema ty (NestedLabeledField l f α φ) ->
    lookup_field_in_type schema ty f = Some fld ->
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema (return_type fld) (β__φ (NestedLabeledField l f α φ) qs).
  Proof.
    elim: qs => // hd tl IH Hqc Hlook.
    case: hd => // [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t χ] /=;
    case Hobj : is_object_type => //= /and3P [Hty Hg Hgs]; simp β__subqueryextract.

     case: eqP => //=; [case: eqP => //= | by intros; apply: IH];
                    [case: eqP => //= | by intros; apply: IH];
                    [rewrite -are_grounded_2_cat //=| by intros; apply: IH].

    - move=> _ Hfeq _; split.
        by move: Hg; simp is_grounded_2; rewrite -Hfeq Hlook /=.
        by apply: IH.
  Qed.
  
  Lemma β__φ_preserves_grounded_inline schema ty t φ qs :
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema t (β__φ (InlineFragment t φ) qs).
  Proof.
    elim: qs => // hd tl IH.
    case: hd => // [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ] /=;
    case Hobj : is_object_type => //= /and3P [Hty Hg Hgs]; simp β__subqueryextract.

    case: eqP => //= Heq; [ | by apply: IH].
    rewrite -are_grounded_2_cat; split=> //.
    rewrite Heq ?are_grounded_2E in Hg *.
    move: Hg; simp is_grounded_2 => /and3P [Ht Hflds Hg].
    apply_andP. orL; apply_andP.
      by apply: IH.
  Qed.
  
  Lemma β__φ_preserves_all_fields schema ty t φ qs :
    is_object_type schema ty = false ->
    are_grounded_2 schema ty qs ->
    all is_field (β__φ (InlineFragment t φ) qs).
  Proof.
    move=> Hscope.
    elim: qs => // hd tl IH.
    case: hd => //.

    all: do ?[by intros => /=; move: H => /=; rewrite Hscope /= => /and3P [_ _ Hgs];
              simp β__subqueryextract; rewrite cat0s; apply: IH].

    move=> t' χ /=; rewrite Hscope /= => /and3P [Hty Hg Hgs].
    simp β__subqueryextract.
    case: eqP => //= Heq; last by apply: IH.
    rewrite all_cat; apply_andP; last by apply: IH.
      by move: Hg; simp is_grounded_2 => /and3P [_ H _].
  Qed.
  
  Lemma remove_redundancies_preserves_grounded schema qs :
    forall ty,
    all (query_conforms schema ty) qs ->
    are_grounded_2 schema ty qs ->
    are_grounded_2 schema ty (remove_redundancies qs).
  Proof.
    apply_funelim (remove_redundancies qs) => // [f α | l f α | f α φ | l f α φ | t φ] tl IHtl.
    all: do ?[ move=> ty;
               all_cons => [Hqc Hqsc] /=;
               case Hobj : is_object_type => //= /and3P [Hf Hg Hgs];
                 by apply_and3P; apply: γ__φ_preserves_grounded; apply: IHtl].

    - move=> IH ty.
      all_cons => [Hqc Hqsc] /=.
      case Hobj : is_object_type => //= /and3P [Hf Hg Hgs].
      apply_and3P; simp is_grounded_2.
      case Hlook: lookup_field_in_type => [fld|] //=.
      apply: IH.
      * rewrite all_cat; apply_andP.
        by move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _]. 
      * by apply: (β__φ_preserves_conformance_nf schema ty) => //.
      * rewrite -are_grounded_2_cat; split.
        + by move: Hg; simp is_grounded_2; rewrite Hlook /=.
        + by apply: (β__φ_preserves_grounded_nf schema ty).
      * by rewrite /query_conforms Hlook in Hqc.
      * by apply: γ__φ_preserves_grounded; apply: (IHtl ty).

    - move=> IH ty.
      all_cons => [Hqc Hqsc] /=.
      case Hobj : is_object_type => //= /and3P [Hf Hg Hgs].
      apply_and3P; simp is_grounded_2.
      case Hlook: lookup_field_in_type => [fld|] //=.
      apply: IH.
      * rewrite all_cat; apply_andP.
        by move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _]. 
      * by apply: (β__φ_preserves_conformance_nlf schema ty) => //.
      * rewrite -are_grounded_2_cat; split.
        + by move: Hg; simp is_grounded_2; rewrite Hlook /=.
        + by apply: (β__φ_preserves_grounded_nlf schema ty).
      * by rewrite /query_conforms Hlook in Hqc.
      * by apply: γ__φ_preserves_grounded; apply: (IHtl ty).

    - move=> IH ty.
      all_cons => [Hqc Hqsc] /=.
      case Hobj : is_object_type => //= /and3P [Hf Hg Hgs].
      apply_and3P; simp is_grounded_2; last first.
        by apply: γ__φ_preserves_grounded; apply: IHtl.
      move: Hg; simp is_grounded_2 => /and3P [Htobj Hflds Hg].
      apply_and3P.
      * apply: remove_redundancies_preserves_all_fields; rewrite all_cat; apply_andP.
          by apply: (β__φ_preserves_all_fields schema ty).
      * have H: forall qs, are_grounded_2 schema t qs -> all (is_grounded_2 schema t) qs.
          by move=> qs'; rewrite are_grounded_2E => /andP [_].
        apply: H.
        apply: IH.
        rewrite all_cat; apply_andP.
          by move: Hqc; query_conforms; move=> [_ _ _].
          by apply: (β__φ_preserves_conformance_inline schema ty).
        rewrite -are_grounded_2_cat; split=> //.
        rewrite are_grounded_2E.
        apply_andP; orL; apply_andP.
        by apply: (β__φ_preserves_grounded_inline schema ty).
  Qed.

  Lemma obj_spreads_if_in_possible_types_of_interface schema ty ti :
    is_object_type schema ty ->
    is_interface_type schema ti ->
    ty \in get_possible_types schema ti ->
           is_fragment_spread_possible schema ti ty.
  Proof.
    move=> Hobj Hintf Hin.
    rewrite /is_fragment_spread_possible.
    rewrite (get_possible_types_interfaceE Hintf) in Hin *.
    by rewrite get_possible_types_objectE // fset1I Hin.
  Qed.

 
    
  Lemma normalize__φ_preserves_conformance schema ty qs :
    all (query_conforms schema ty) qs ->
    all (query_conforms schema ty) (normalize__φ schema ty qs).
  Proof.
    elim: qs => // hd tl IH.
    all_cons => [Hqc Hqsc].
    case: hd Hqc => // [f α | l f α | f α φ | l f α φ | t φ ] Hqc /=;
    rewrite all_cat; apply_andP; simp normalize.

    all: do ?[case Hscope : is_object_type => //=].
    all: do ?[by move: Hqc; rewrite /query_conforms; case lookup_field_in_type => // fld;
              move/andP => [Hty Hargs]; do ? apply_andP].

    rewrite all_fset; apply/allP=> x /mapP [q Hin ->].
    apply/and4P; split=> //.
    * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
    * move: (in_possible_types_is_object Hin) => Hobj.
      have Hfld : is_field (SingleField f α) by [].
      move: (scope_is_obj_or_abstract_for_field Hfld Hqc) => [Hcontr | Hintf]; [by rewrite Hscope in Hcontr|].
        by apply: obj_spreads_if_in_possible_types_of_interface.
    * rewrite -/(query_conforms _ _) [query_conforms]lock all_seq1 -lock.
      have Hfld : is_field (SingleField f α) by [].
      move: (scope_is_obj_or_abstract_for_field Hfld Hqc) => [Hcontr | Hintf]; [by rewrite Hscope in Hcontr|].
      rewrite get_possible_types_interfaceE // in Hin.
        by apply (sf_conforms_in_interface_in_obj Hin).

     rewrite all_fset; apply/allP=> x /mapP [q Hin ->].
    apply/and4P; split=> //.
    * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
    * move: (in_possible_types_is_object Hin) => Hobj.
      have Hfld : is_field (SingleField f α) by []. (* It's valid bc query conforms is the same for labeled and normal? *)
      move: (scope_is_obj_or_abstract_for_field Hfld Hqc) => [Hcontr | Hintf]; [by rewrite Hscope in Hcontr|].
        by apply: obj_spreads_if_in_possible_types_of_interface.
    * rewrite -/(query_conforms _ _) [query_conforms]lock all_seq1 -lock.
      have Hfld : is_field (SingleField f α) by [].
      move: (scope_is_obj_or_abstract_for_field Hfld Hqc) => [Hcontr | Hintf]; [by rewrite Hscope in Hcontr|].
      rewrite get_possible_types_interfaceE // in Hin.
        by apply (sf_conforms_in_interface_in_obj Hin).

    - case Hscope : (is_object_type schema ty);
      move: Hqc; rewrite /query_conforms. case Hlook: lookup_field_in_type => [fld|] //= /and4P [Hty Hargs Hne Hfqsc];
      rewrite Hscope /= Hlook.
      apply_andP; apply/and4P; split=> //.

      
        
  Lemma remove_redundancies_preserves_grounded_normalize schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs)).
  Proof.
    move=> Hqsc Hvs.
    apply: remove_redundancies_preserves_grounded => //.
      by apply: normalize__φ_preserves_conformance.
      by apply: normalize__φ_are_grounded
          
        
  Lemma remove_redundancies_preserves_grounded_normalize schema ty q :
    query_conforms schema ty q ->
    has_valid_fragments schema ty q ->
    is_grounded_2 schema ty (remove_redundancies__φ q).
  Proof.

    funelim (remove_redundancies__φ q) => //.
    intros.
    simp is_grounded_2; case Hlook: lookup_field_in_type => [fld|] //=.
    move: H0; simp is_grounded_2; rewrite Hlook /=.
    elim: l H => // hd tl IH.
    
    
    elim q using Query_ind with
        (Pl := fun qs =>
                forall ty qs',
                  all (query_conforms schema ty) qs ->
                  are_grounded_2 schema ty qs ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty (remove_redundancies (qs ++ qs')));
      simp remove_redundancies__φ.


            
    - move=> f α φ IH ty; simp remove_redundancies__φ; simp is_grounded_2 => Hqc.
      case Hlook: lookup_field_in_type => [fld|] //=.
      move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _ Hqsc] Hgs.
        by move: (IH fld.(return_type) [::] Hqsc Hgs are_grounded_nil are_non_redundant_nil); rewrite cats0.
        
    - move=> l f α φ IH ty; simp remove_redundancies__φ; simp is_grounded_2 => Hqc.
      case Hlook: lookup_field_in_type => [fld|] //=.
      move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _ Hqsc] Hgs.
        by move: (IH fld.(return_type) [::] Hqsc Hgs are_grounded_nil are_non_redundant_nil); rewrite cats0.


    - move=> t φ IH ty; simp remove_redundancies__φ; simp is_grounded_2.
      query_conforms; move=> [_ _ _ Hqsc].
      move/andP=> [Ht].
      have Heq : all is_field φ && all (is_grounded_2 schema t) φ = are_grounded_2 schema t φ.
        by rewrite are_grounded_2E Ht orbF andTb.
      move=> Hg.
      apply_and3P.
        by apply: remove_redundancies_preserves_all_fields; move/andP: Hg; case.
      rewrite Heq in Hg.
      by move: (IH t [::] Hqsc Hg are_grounded_nil are_non_redundant_nil); rewrite cats0 are_grounded_2E => /andP [_].

    - move=> ty qs' _ _ Hg Hnr.
        by rewrite cat0s non_redundant_eq_remove.

        
    - move=> hd IHhd tl IHtl ty qs'.
      all_cons => [Hqc Hqsc] Hg Hgs' Hnr.
      rewrite cat_cons.
      move: Hg; rewrite are_grounded_2_equation_2.
      case: hd IHhd Hqc => [f α | l f α | f α φ | l f α φ | t φ] IHhd Hqc;
      simp remove_redundancies => /=; case Hobj : is_object_type => /= /and3P [Hty Hg Hgs]; apply_and3P;
      simp is_grounded_2; rewrite -/(cat _ _).
      all: do?[by apply: γ__φ_preserves_grounded; apply: IHtl].

      
      * case Hlook: lookup_field_in_type => //= [fld|].
        
        move: (IHhd ty Hqc Hg).
        simp remove_redundancies__φ; simp is_grounded_2; rewrite Hlook /=.
  Abort.
    
  Lemma remove_redundancies_preserves_grounded_cat :
    forall schema ty qs qs',
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (query_conforms schema ty) qs' ->
      all (has_valid_fragments schema ty) qs' ->
      are_grounded_2 schema ty qs' ->
      are_non_redundant qs' ->
      are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs ++ qs')).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                forall qs',
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty (remove_redundancies (nqs ++ qs')))
             (fun schema ty qs nqs =>
                forall qs',
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty (remove_redundancies (nqs ++ qs'))));
      move=> schema.
    
    all: do ?[by intros; move: H0; rewrite /query_conforms Heq].

    - intros.
      rewrite cat1s; simp remove_redundancies => /=; rewrite Heq /=.
      apply_and3P.
      apply: γ__φ_preserves_grounded.
      apply_andP.
      orL; apply_andP.
      apply: filter_preserves_pred.
      apply: remove_redundancies_preserves_all_fields.
        by apply: (are_grounded_in_object_scope_are_fields schema s).
      apply_andP.
      apply: filter_preserves_pred.
      rewrite non_redundant_eq_remove //.
        by move: (are_grounded_2_in_normal_form schema qs' s H1 H3); rewrite /are_in_normal_form => /andP [_].
      
    - intros => /=.
      rewrite /are_in_normal_form; apply_andP.
      orR.
      apply: remove_redundancies_preserves_all_inlines.
      rewrite all_cat; apply_andP; last first.
      apply (are_grounded_in_abstract_scope_are_inlines schema s) => //.
        by apply: (type_in_scope_N_obj_is_abstract H Heq).
        by apply/allP=> x /mapP [q _ ->].

      admit.

    - intros.
      rewrite cat1s.
      simp remove_redundancies => /=.
      rewrite /are_in_normal_form.
      apply_andP.
      orL; apply_andP.
      apply: filter_preserves_pred.
      apply: remove_redundancies_preserves_all_fields.
      move: H5; rewrite /have_same_shape.
      case=> [[_ Hfld] | [Hcontr _]] //.
      apply_andP.
      apply: filter_preserves_pred.
      rewrite non_redundant_eq_remove //.
        by move: H3; are_in_normal_form.

    - intros.

    - intros. simpl.
      Admitted.
      
    - move=> 
                


  Lemma remove_redundancies_preserves_grounded :
    forall schema ty query,
      query_conforms schema ty query ->
      has_valid_fragments schema ty query ->
      are_grounded_2 schema ty (remove_redundancies (normalize schema ty query)).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                 query_conforms schema ty q ->
                 has_valid_fragments schema ty q ->
                 are_grounded_2 schema ty (remove_redundancies nqs))
             (fun schema ty qs nqs =>
                 all (query_conforms schema ty) qs ->
                 all (has_valid_fragments schema ty) qs ->
                 are_grounded_2 schema ty (remove_redundancies nqs))) => schema.

    all: do ?[by intros; simp remove_redundancies => /=; rewrite Heq /=; apply/and3P; split].
  
    all: do?[by intros; rewrite /query_conforms Heq in H].

    all: do?[intros => /=;
             rewrite remove_redundancies_inlined_query; simp remove_redundancies => /=;
             rewrite are_grounded_2E; apply_andP;
             [orR; apply_andP; [rewrite Heq //|];
               by rewrite all_fset; apply/allP=> x /mapP [q _ ->] |
             rewrite all_fset; apply/allP=> x /mapP [q Hin ->]; simp is_grounded_2;
               by apply_and3P; apply: (in_possible_types_is_object Hin)]].
   
    all: do?[intros; simp remove_redundancies => /=; rewrite cats0 Heq /=;
             apply_and3P;
             simp is_grounded_2; move: H0; rewrite /query_conforms Heq0 /= => /and4P [_ _ _ Hqsc];
             move: H1; simp has_valid_fragments; rewrite Heq0 /= => Hv;
               by apply: H].
      
    - intros => /=.
    rewrite remove_redundancies_inlined_query; simp remove_redundancies => /=; rewrite cats0.
    rewrite are_grounded_2E; apply_andP.
      by orR; apply_andP; [rewrite Heq | rewrite all_fset; apply/allP=> x /mapP [q _ ->]].

      rewrite all_fset; apply/allP=> x /mapP [q Hin ->]; simp is_grounded_2.
      apply_and3P.
      apply: (in_possible_types_is_object Hin).
      rewrite all_seq1; simp is_grounded_2.
      rewrite get_possible_types_interfaceE in Hin.
      move: (field_in_interface_in_object_same_return_type Hin Heq0) => [fld' -> Hrty] /=.
      move: H0; rewrite /query_conforms Heq0 /= => /and4P [_ _ _ Hqsc].
      move: H1; simp has_valid_fragments; rewrite Heq0 /= => Hv.
        by rewrite -Hrty; apply: H.
        have Hf: is_field (NestedField s3 f1 l) by [].
        by move: (scope_is_obj_or_abstract_for_field  Hf H0) => [Hcontr | //]; rewrite Heq in Hcontr.

            
    - intros => /=.
    rewrite remove_redundancies_inlined_query; simp remove_redundancies => /=; rewrite cats0.
    rewrite are_grounded_2E; apply_andP.
      by orR; apply_andP; [rewrite Heq | rewrite all_fset; apply/allP=> x /mapP [q _ ->]].

      rewrite all_fset; apply/allP=> x /mapP [q Hin ->]; simp is_grounded_2.
      apply_and3P.
      apply: (in_possible_types_is_object Hin).
      rewrite all_seq1; simp is_grounded_2.
      rewrite get_possible_types_interfaceE in Hin.
      move: (field_in_interface_in_object_same_return_type Hin Heq0) => [fld' -> Hrty] /=.
      move: H0; rewrite /query_conforms Heq0 /= => /and4P [_ _ _ Hqsc].
      move: H1; simp has_valid_fragments; rewrite Heq0 /= => Hv.
        by rewrite -Hrty; apply: H.
        have Hf: is_field (NestedLabeledField s4 s5 f2 l0) by [].
        by move: (scope_is_obj_or_abstract_for_field  Hf H0) => [Hcontr | //]; rewrite Heq in Hcontr.

    - move=> t b ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ _ Hqsc].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/eqP Heq Hv]; rewrite Heq in Hqsc.
        by apply: IH.

    - move=> t ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ _ Hqsc].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Hcontr | _] Hv].
        by rewrite Hcontr in Ht; rewrite Ht in Hscope.
      simp remove_redundancies => /=; rewrite Hscope /= cats0.
      apply_and3P; simp is_grounded_2; apply_and3P.
      apply: remove_redundancies_preserves_all_fields.
        by apply: normalize__φ_in_object_scope_are_fields.
      by move: (IH Hqsc Hv); rewrite are_grounded_2E => /andP [_].

    - move=> t ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ _ Hqsc].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv]; last first.
        by rewrite Hcontr in Ht.
      by rewrite Heq in Hqsc Hv; apply: IH.
        
    - move=> ty hd tl IHhd IHtl.
      all_cons => [Hqc Hqsc].
      all_cons => [Hv Hvs].
      



      
  
 Lemma remove_redundancies_preserves_normal_form_cat 
    forall schema ty qs qs',
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (query_conforms schema ty) qs' ->
      all (has_valid_fragments schema ty) qs' ->
      are_grounded_2 schema ty qs' ->
      are_non_redundant qs' ->
      are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs ++ qs')).
  Proof.
    apply (normalize_elim
             (fun schema ty q nq =>
                forall qs',
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_grounded_2 schema ty (remove_redundancies (nq ++ qs')))
             (fun schema ty qs nqs =>
                forall qs',
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty (remove_redundancies (nqs ++ qs'))));
      move=> schema //.
    

    - intros.
      rewrite cat1s.
      simp remove_redundancies => /=; rewrite Heq /=.
      apply/and3P; split=> //.
      
      apply_andP.
      orL; apply_andP.
      apply: filter_preserves_pred.
      apply: remove_redundancies_preserves_all_fields.
        by apply: (are_grounded_in_object_scope_are_fields schema s).
      apply_andP.
      apply: filter_preserves_pred.
      rewrite non_redundant_eq_remove //.
        by move: (are_grounded_2_in_normal_form schema qs' s H1 H3); rewrite /are_in_normal_form => /andP [_].
      
    - intros => /=.
      rewrite /are_in_normal_form; apply_andP.
      orR.
      apply: remove_redundancies_preserves_all_inlines.
      rewrite all_cat; apply_andP; last first.
      apply (are_grounded_in_abstract_scope_are_inlines schema s) => //.
        by apply: (type_in_scope_N_obj_is_abstract H Heq).
        by apply/allP=> x /mapP [q _ ->].


  Lemma remove_redundancies_preserves_normal_form_cat :
    forall schema ty qs qs',
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (query_conforms schema ty) qs' ->
      all (has_valid_fragments schema ty) qs' ->
      are_grounded_2 schema ty qs' ->
      are_non_redundant qs' ->
      are_in_normal_form schema (remove_redundancies (normalize__φ schema ty qs ++ qs')).
  Proof.
    apply (normalize_elim
             (fun schema ty q nq =>
                forall qs',
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_in_normal_form schema (remove_redundancies (nq ++ qs')))
             (fun schema ty qs nqs =>
                forall qs',
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  all (query_conforms schema ty) qs' ->
                  all (has_valid_fragments schema ty) qs' ->
                  are_grounded_2 schema ty qs' ->
                  are_non_redundant qs' ->
                  are_in_normal_form schema (remove_redundancies (nqs ++ qs'))));
      move=> schema //.
    
    all: do ?[by intros; move: H0; rewrite /query_conforms Heq].

    - intros.
      rewrite cat1s.
      simp remove_redundancies => /=.
      rewrite /are_in_normal_form.
      apply_andP.
      orL; apply_andP.
      apply: filter_preserves_pred.
      apply: remove_redundancies_preserves_all_fields.
        by apply: (are_grounded_in_object_scope_are_fields schema s).
      apply_andP.
      apply: filter_preserves_pred.
      rewrite non_redundant_eq_remove //.
        by move: (are_grounded_2_in_normal_form schema qs' s H1 H3); rewrite /are_in_normal_form => /andP [_].
      
    - intros => /=.
      rewrite /are_in_normal_form; apply_andP.
      orR.
      apply: remove_redundancies_preserves_all_inlines.
      rewrite all_cat; apply_andP; last first.
      apply (are_grounded_in_abstract_scope_are_inlines schema s) => //.
        by apply: (type_in_scope_N_obj_is_abstract H Heq).
        by apply/allP=> x /mapP [q _ ->].

      admit.

    - intros.
      rewrite cat1s.
      simp remove_redundancies => /=.
      rewrite /are_in_normal_form.
      apply_andP.
      orL; apply_andP.
      apply: filter_preserves_pred.
      apply: remove_redundancies_preserves_all_fields.
      move: H5; rewrite /have_same_shape.
      case=> [[_ Hfld] | [Hcontr _]] //.
      apply_andP.
      apply: filter_preserves_pred.
      rewrite non_redundant_eq_remove //.
        by move: H3; are_in_normal_form.

    - intros.

    - intros. simpl.
      Admitted.
      
      
      
  
  Lemma remove_redundancies_preserves_normal_form :
     forall schema type_in_scope query,
       query_conforms schema type_in_scope query ->
       has_valid_fragments schema type_in_scope query -> 
       are_in_normal_form schema (remove_redundancies (normalize schema type_in_scope query)).
   Proof.
     apply (normalize_elim
              (fun schema ty q nq =>
                 query_conforms schema ty q ->
                 has_valid_fragments schema ty q ->
                 are_in_normal_form schema (remove_redundancies nq))
              (fun schema ty qs nqs =>
                 all (query_conforms schema ty) qs ->
                 all (has_valid_fragments schema ty) qs ->
                 are_in_normal_form schema (remove_redundancies nqs)));
       move=> schema.

     all: do ?[by intros; simp remove_redundancies => /=;
               rewrite /are_in_normal_form; apply/andP; split].

     - move=> ty f α Hobj Hqc Hv.
       rewrite remove_redundancies_inlined_query /=.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //.
       
       by orR; apply/allP=> q /mapP [t _ ->].
       apply/allP=> q /mapP [t H ->] /=.
       simp is_in_normal_form; apply/and3P; split=> //.
       by apply: (in_possible_types_is_object H).
     - move=> ty l f α Hobj Hqc Hv.
       rewrite remove_redundancies_inlined_query /=.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //.
       
       by orR; apply/allP=> q /mapP [t _ ->].
       apply/allP=> q /mapP [t H ->] /=.
       simp is_in_normal_form; apply/and3P; split=> //.
       by apply: (in_possible_types_is_object H).

     - move=> ty  f fld α φ IH Hobj Hlook Hqc Hv.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //=.
       apply/andP; split=> //; simp is_in_normal_form.
       rewrite -/(are_in_normal_form _ _).
       simp β__φ => /=. rewrite cats0.
       move: Hqc Hv; simp has_valid_fragments; rewrite /query_conforms Hlook /= => /and4P [_ _ _ Hqc] Hv.
         by apply: (IH Hqc Hv).
         
     - move=> ty f fld α φ IH Hobj Hlook Hqc Hv.
       rewrite remove_redundancies_inlined_query /=.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //=.
         by orR; apply/allP=> q /mapP [t _ ->].
       apply/allP=> q /mapP [t H ->] /=.
       simp is_in_normal_form; apply/and3P; split=> //.
       by apply: (in_possible_types_is_object H).

       rewrite /all; apply/andP; split=> //.
       simp is_in_normal_form; rewrite -/(are_in_normal_form _ _).
       simp β__φ => /=. rewrite cats0.
       move: Hqc Hv; simp has_valid_fragments; rewrite /query_conforms Hlook /= => /and4P [_ _ _ Hqc] Hv.
       by apply: (IH Hqc Hv).
       
     - move=> ty f fld l α φ IH Hobj Hlook Hqc Hv.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //=.
       apply/andP; split=> //; simp is_in_normal_form.
       rewrite -/(are_in_normal_form _ _).
       simp β__φ => /=. rewrite cats0.
       move: Hqc Hv; simp has_valid_fragments; rewrite /query_conforms Hlook /= => /and4P [_ _ _ Hqc] Hv.
         by apply: (IH Hqc Hv).
         
     - move=> ty f fld l α φ IH Hobj Hlook Hqc Hv.
       rewrite remove_redundancies_inlined_query /=.
       simp remove_redundancies => /=.
       rewrite /are_in_normal_form; apply/andP; split=> //=.
         by orR; apply/allP=> q /mapP [t _ ->].
       apply/allP=> q /mapP [t H ->] /=.
       simp is_in_normal_form; apply/and3P; split=> //.
       by apply: (in_possible_types_is_object H).

       rewrite /all; apply/andP; split=> //.
       simp is_in_normal_form; rewrite -/(are_in_normal_form _ _).
       simp β__φ => /=. rewrite cats0.
       move: Hqc Hv; simp has_valid_fragments; rewrite /query_conforms Hlook /= => /and4P [_ _ _ Hqc] Hv.
       by apply: (IH Hqc Hv).

     - move=> ty b t φ IH Hscope Ht Hqc Hv.
       move: Hqc; query_conforms.
       move=> [_ _ Hne Hqc].
       move: Hv; simp has_valid_fragments; rewrite Ht /= => /andP [/eqP Heq H].
       rewrite Heq in Hqc.
       by apply: (IH Hqc H).

     - move=> t ty φ IH Ht Hscope Hqc Hv.
       simp remove_redundancies; simp β__φ; rewrite cats0 /=.
       rewrite /are_in_normal_form; apply/andP; split=> //=.
       apply/andP; split=> //.       
       move: Hqc; query_conforms.
       move=> [_ _ _ Hqsc].
       move: Hv; simp has_valid_fragments; rewrite Hscope => /andP [_ Hvs].
       move: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Ht).
       move: (IH Hqsc Hvs); rewrite /are_in_normal_form => /andP [_ H] Hfld.
       simp is_in_normal_form; apply/and3P; split=> //.
         by apply: (remove_redundancies_preserves_all_fields _ Hfld).

     - move=> t ty φ IH Ht Hscope Hqc Hv.
       move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv]; last first.
         by rewrite Hcontr in Ht.
       rewrite Heq in Hqc Hv.
       move: Hqc; query_conforms.
       move=> [_ _ _ Hqsc].
         by apply: (IH Hqsc Hv).

     - move=> ty hd tl IH IH'.
       all_cons => [Hqc Hqsc].
       all_cons => [Hv Hvs].
       move: (type_in_scope_N_scalar_enum Hqc) => [Hobj | Hintf | Hunion].

       * case: hd IH Hqc Hv => [ f α
                              | l f α
                              | f α φ
                              | l f α φ
                              | t φ] IH Hqc Hv;
         simp normalize; rewrite ?Hobj /=; simp remove_redundancies => /=.

         all: do ?[rewrite /are_in_normal_form; apply_andP].
         all: do ?[apply: filter_preserves_pred].
         all: do ?[move: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Hobj);
                     by apply: remove_redundancies_preserves_all_fields].
         all: do ?[by move: (IH' Hqsc Hvs); rewrite /are_in_normal_form => /andP [_ H]].

       + move/nf_conformsP: Hqc => [fld Hlook _];
         rewrite Hlook /= Hobj /=; simp remove_redundancies. simpl.
         apply/andP; split=> //.
         apply: filter_preserves_pred.
         move: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Hobj).
         by apply: remove_redundancies_preserves_all_fields.
       + set Hqc2 := Hqc.
         move/nf_conformsP: Hqc2 => [fld Hlook /and3P [Hfty _ Hqsc']];
         rewrite Hlook /= Hobj /=; simp remove_redundancies => /=.
         apply/andP; split=> //; last first.
         apply: filter_preserves_pred.
           by move: (IH' Hqsc Hvs); rewrite /are_in_normal_form => /andP [_].
           simp is_in_normal_form; rewrite -/(are_in_normal_form _ _).
           apply: remove_redundancies_preserves_normal_form_cat => //.
           (*by move: Hqsc'; rewrite /queries_conform => /andP [_].
           by move: Hv; simp has_valid_fragments; rewrite Hlook /=.*)
           admit.
           admit.
           admit.
           admit.
           admit.
           admit.
           admit.
           case/orP: Hfty => [Hfobj | Hfabs];
           rewrite /have_same_shape; [left | right]; split;
           move: Hv; simp has_valid_fragments; rewrite Hlook /= => Hfvs;
           move: Hqsc'; rewrite /queries_conform => /andP [_ Hfqcs].
             by apply (normalize__φ_in_object_scope_are_fields _ _ _ Hfqcs Hfvs Hfobj).
           apply: β__φ_nf_fields => //. exact: Hlook. done.
             by apply (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hfqcs Hfvs Hfabs).
           apply: β__φ_nf_inlines => //. exact: Hlook. done.

       + move/nlf_conformsP: Hqc => [fld Hlook _];
         rewrite Hlook /= Hobj /=; simp remove_redundancies.
         apply/andP; split=> //.
         apply: filter_preserves_pred.
         move: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Hobj).
         by apply: remove_redundancies_preserves_all_fields.
       + move/nlf_conformsP: Hqc => [fld Hlook H];
         rewrite Hlook /= Hobj /=; simp remove_redundancies.
         apply/andP; split=> //; last first.
         apply: filter_preserves_pred.
           by move: (IH' Hqsc Hvs); rewrite /are_in_normal_form => /andP [_].
           (* simp is_in_normal_form; rewrite -/(are_in_normal_form _ _) *)
         simp is_in_normal_form; apply/andP; split.
         move/and3P: H => [/orP [Hfobj | Hfabs] _ Hfqcs]; [orL | orR];                          
         move: Hv; simp has_valid_fragments; rewrite Hlook /= => Hfvs;
         move: Hfqcs; rewrite /queries_conform => /andP [_ Hfqcs];
         [apply: remove_redundancies_preserves_all_fields | apply: remove_redundancies_preserves_all_inlines];
         rewrite all_cat; apply/andP; split.
           by apply (normalize__φ_in_object_scope_are_fields _ _ _ Hfqcs Hfvs Hfobj).
           admit.
           by apply (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hfqcs Hfvs Hfabs).
           admit.
         admit.

       + orL.
         apply: remove_redundancies_preserves_all_fields.
         rewrite all_cat; apply/andP; split.
         move: Hv; simp has_valid_fragments; rewrite Hobj /= => /andP [/eqP Heq Hv].
         move: Hqc; query_conforms.
         move=> [_ _ _ Hqc].
         rewrite Heq in Hqc.
           by apply: (normalize__φ_in_object_scope_are_fields _ _ _ Hqc Hv Hobj).
          by apply: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Hobj).
          admit.   

       * orR; apply: remove_redundancies_preserves_all_inlines.
         by rewrite all_cat; apply/andP; split;
           move/is_interface_is_abstract: Hintf => Habs;
           [ apply: normalize_in_abstract_scope_are_inlines
           | apply: normalize__φ_in_abstract_scope_are_inlines].

         +  admit.

       * orR; apply: remove_redundancies_preserves_all_inlines.
         by rewrite all_cat; apply/andP; split;
           move/is_union_is_abstract: Hunion => Habs;
           [ apply: normalize_in_abstract_scope_are_inlines
           | apply: normalize__φ_in_abstract_scope_are_inlines].

         + admit.
           

      
End QueryRewrite.

