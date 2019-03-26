
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


  

  Ltac apply_andP := apply/andP; split=> //.
  Ltac are_in_normal_form := rewrite /are_in_normal_form => /andP; case.
  


  Equations normalize schema : @NamedType Name -> @Query Name Vals -> seq (@Query Name Vals) :=
    {
      normalize _ type_in_scope (SingleField f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: SingleField f α];
        | _ := let possible_types := get_possible_types schema type_in_scope in
              [seq (InlineFragment ty [:: (SingleField f α)]) | ty <- possible_types]
        };

       normalize schema  type_in_scope (LabeledField l f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: LabeledField l f α];
        | _ := let possible_types := get_possible_types schema type_in_scope in
              [seq (InlineFragment ty [:: (LabeledField l f α)]) | ty <- possible_types]
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
                [seq (InlineFragment ty [:: NestedField f α normalized_head]) | ty <- possible_types]
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
                [seq (InlineFragment ty [:: NestedLabeledField l f α normalized_head]) | ty <- possible_types]
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

 
  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.

 
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
      all: do ?[by intros; simp normalize; rewrite Heq /=; apply/allP => x /mapP [t _ ->]].
      all: do ?[by intros; rewrite /query_conforms in H; case Hlook : lookup_field_in_type in H; rewrite Hlook in Heq].
      all: do ?[by intros; simp normalize; case lookup_field_in_type => // fld /=;
                move: (abstract_type_N_obj H2) => -> /=; apply/allP=> x /mapP [t _ ->]].

    - by intros; move: (abstract_type_N_obj H2) => Hcontr; rewrite Hcontr in Heq0.
    - by intros; simp normalize; rewrite Heq Heq0 /=.
    - intros; simp normalize; rewrite Heq Heq0 /=.
      move: H0; query_conforms.
      move=> [_ _ _ Hqc].
      move: H1; simp has_valid_fragments; rewrite Heq0 /= => /andP [/orP [/eqP Heq' | Hcontr] Hv]; last first.
      by rewrite Hcontr in Heq.
      apply: H; rewrite -Heq' in H2 * => //.
      
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
    all: do ?[by move: (abstract_type_N_obj H1) => -> /=;
              apply/allP=> x /mapP [t _ ->]].
    all: do ?[by case: lookup_field_in_type => [fld|] //=;
              move: (abstract_type_N_obj H1) => -> /=;
              apply/allP=> x /mapP [t _ ->]].

    move: H0; simp has_valid_fragments.
    move: (abstract_type_N_obj H1) => Hnobj.
    rewrite Hnobj /= => /andP [/orP [/eqP Heq | Hobj] Hv].
    move: H; query_conforms.
    move=> [_ _ _ Hqsc].
    rewrite Heq Hnobj in Hqsc Hv *.
      by apply: normalize__φ_in_abstract_scope_are_inlines.
        by rewrite Hobj /=; apply/andP.
  Qed.
  
  Ltac orL := apply/orP; left.
  Ltac orR := apply/orP; right.
  
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
   
  Equations β__φ (flt : @Query Name Vals) (queries : seq (@Query Name Vals)) : seq (@Query Name Vals) :=
    {
      β__φ _ [::] := [::];
      β__φ flt (cons hd tl) := (β__subqueryextract flt hd) ++ (β__φ flt tl)
    }.

  Lemma β__subqueryextract_size_reduced flt q :
    queries_size (β__subqueryextract flt q) < query_size q.
  Proof.
    by apply_funelim (β__subqueryextract flt q) => //=; intros; case: q0; intros; simp query_size.
  Qed.
  
  Lemma β__φ_size_reduced flt queries :
    queries_size (β__φ flt queries) <= queries_size queries.
  Proof.
    funelim (β__φ flt queries) => //=.
    rewrite queries_size_app.
    move: (β__subqueryextract_size_reduced flt q) => Hlt.
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
    move=> hd tl IH x.
    simp β__φ.
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

    
    
  Obligation Tactic := intros; simp query_size; do ? ssromega.  
  Equations remove_redundancies (queries : seq (@Query Name Vals)) : seq (@Query Name Vals)
    by wf (queries_size queries) lt :=
    {
      remove_redundancies nil := [::];
      
      remove_redundancies ((SingleField f α) :: queries) :=
        let filtered := remove_redundancies queries in
        (SingleField f α) :: (γ__φ (SingleField f α) filtered) ;
      
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
    rewrite queries_size_app.
    move: (β__φ_size_reduced (NestedField f α φ) queries) => Hlt.
    by ssromega.
  Qed.
  Next Obligation.
     simp query_size; rewrite queries_size_app.
     move: (β__φ_size_reduced (NestedLabeledField l f α φ) queries) => Hlt.
    by ssromega.
  Qed.
  Next Obligation.
     simp query_size; rewrite queries_size_app.
     move: (β__φ_size_reduced (InlineFragment t φ) queries) => Hlt.
    by ssromega.
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
  
  Lemma remove_redundancies_preserves_normal_form schema queries :
    are_in_normal_form schema queries ->
    are_in_normal_form schema (remove_redundancies queries).
  Proof.
    apply_funelim (remove_redundancies queries) => //.
    - move=> f α tl IH.
      move/are_in_normal_form_E=> /= [[/andP [Hf Hfs] | //] /andP [Hnf Hnfs]].
      apply/and3P; split=> //.
      orL; apply/andP; split => //.
      apply: filter_preserves_pred.
      by apply: remove_redundancies_preserves_all_fields.
      apply: filter_preserves_pred.
      move: (IH (are_in_normal_form_fields_inv _ _  _  _ Hfs Hnfs)).
      by rewrite /are_in_normal_form => /andP [_ H].

    - move=> l f α tl IH.
      move/are_in_normal_form_E=> /= [[/andP [Hf Hfs] | //] /andP [Hnf Hnfs]].
      apply/and3P; split=> //.
      orL; apply/andP; split => //.
      apply: filter_preserves_pred.
      by apply: remove_redundancies_preserves_all_fields.
      apply: filter_preserves_pred.
      move: (IH (are_in_normal_form_fields_inv _ _  _  _ Hfs Hnfs)).
      by rewrite /are_in_normal_form => /andP [_ H].

    - move=> f α φ tl IH IH'.
      move/are_in_normal_form_E=> /= [[/andP [Hf Hfs] | //] /andP [Hnf Hnfs]].
      apply/and3P; split=> //.
      orL; apply/andP; split => //.
      apply: filter_preserves_pred.
      by apply: remove_redundancies_preserves_all_fields.
      simp is_in_normal_form; rewrite -/(are_in_normal_form _ _).
      apply: IH'; rewrite /are_in_normal_form.
  Abort. (* Not necessarily true *)

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


  Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
    

    
    
  Lemma β__φ_nf_fields :
    forall schema ty queries f α φ fld,
    all (query_conforms schema ty) queries ->
    all (has_valid_fragments schema ty) queries ->
    is_object_type schema ty ->
    lookup_field_in_type schema ty f = Some fld ->
    is_object_type schema fld.(return_type) ->
    all is_field (β__φ (NestedField f α φ) (normalize__φ schema ty queries)).
  Proof.

    apply (normalize_elim
             (fun schema ty q nqs =>
                forall f α φ fld, 
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                is_object_type schema ty ->
                lookup_field_in_type schema ty f = Some fld ->
                is_object_type schema fld.(return_type) ->
                all is_field (β__φ (NestedField f α φ) nqs))
             (fun schema ty queries nqs =>
                forall f α φ fld,
                all (query_conforms schema ty) queries ->
                all (has_valid_fragments schema ty) queries ->
                is_object_type schema ty ->
                lookup_field_in_type schema ty f = Some fld ->
                is_object_type schema fld.(return_type) ->
                all is_field (β__φ (NestedField f α φ) nqs)));
      move=> schema.
    all: do ?[by intros; simp β__φ].
    all: do ?[by intros; rewrite Heq in H1].

    all: do ?[by intros; simp β__φ; rewrite cats0;
              simp β__subqueryextract;
              case: eqP => //= _;
              case: ifP => // /eqP Hfeq;
              rewrite Hfeq in H3; rewrite H3 in Heq0; case: Heq0 => Hfldeq;
              move: H0; rewrite /query_conforms H3 => /and4P [_ _ _ Hqc];
              move: H1; simp has_valid_fragments; rewrite H3 /= => Hv;
              apply normalize__φ_in_object_scope_are_fields; rewrite -Hfldeq].

    all: do ?[by intros; rewrite Heq in H2].

  
    intros.
    move: H1; simp has_valid_fragments; rewrite Heq0 /= => /andP [/eqP Hty Hv].
    apply: H => //.
    move: H0; query_conforms.
    move=> [_ _ _ Hqsc].
      by rewrite Hty in Hqsc.
      exact: H3.
      done.

    by intros; rewrite Heq0 in H2.
   
    
    - move=> ty q tl IH IH' f α φ fld.
      all_cons => [Hqc Hqsc].
      all_cons => [Hv Hvs] Hscope Hlook Hfldty.
      rewrite β__φ_cat all_cat; apply/andP; split.
        by apply: (IH f α φ fld).
          by apply: (IH' f α φ fld).
  Qed.


   Lemma β__φ_nf_inlines :
    forall schema ty queries f α φ fld,
    all (query_conforms schema ty) queries ->
    all (has_valid_fragments schema ty) queries ->
    is_object_type schema ty ->
    lookup_field_in_type schema ty f = Some fld ->
    is_abstract_type schema fld.(return_type) ->
    all is_inline_fragment (β__φ (NestedField f α φ) (normalize__φ schema ty queries)).
  Proof.

    apply (normalize_elim
             (fun schema ty q nqs =>
                forall f α φ fld, 
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                is_object_type schema ty ->
                lookup_field_in_type schema ty f = Some fld ->
                is_abstract_type schema fld.(return_type) ->
                all is_inline_fragment (β__φ (NestedField f α φ) nqs))
             (fun schema ty queries nqs =>
                forall f α φ fld,
                all (query_conforms schema ty) queries ->
                all (has_valid_fragments schema ty) queries ->
                is_object_type schema ty ->
                lookup_field_in_type schema ty f = Some fld ->
                is_abstract_type schema fld.(return_type) ->
                all is_inline_fragment (β__φ (NestedField f α φ) nqs)));
      move=> schema.
    all: do ?[by intros; simp β__φ].
    all: do ?[by intros; rewrite Heq in H1].

    all: do ?[by intros; simp β__φ; rewrite cats0;
              simp β__subqueryextract;
              case: eqP => //= _;
              case: ifP => // /eqP Hfeq;
              rewrite Hfeq in H3; rewrite H3 in Heq0; case: Heq0 => Hfldeq;
              move: H0; rewrite /query_conforms H3 => /and4P [_ _ _ Hqc];
              move: H1; simp has_valid_fragments; rewrite H3 /= => Hv;
              apply normalize__φ_in_abstract_scope_are_inlines; rewrite -Hfldeq].

    all: do ?[by intros; rewrite Heq in H2].

    intros.
    move: H1; simp has_valid_fragments; rewrite Heq0 /= => /andP [/eqP Hty Hv].
    apply: (H f α φ fld) => //.
    move: H0; query_conforms.
    move=> [_ _ _ Hqsc].
      by rewrite Hty in Hqsc.

    by intros; rewrite Heq0 in H2.
   
    
    - move=> ty q tl IH IH' f α φ fld.
      all_cons => [Hqc Hqsc].
      all_cons => [Hv Hvs] Hscope Hlook Hfldty.
      rewrite β__φ_cat all_cat; apply/andP; split.
        by apply: (IH f α φ fld).
          by apply: (IH' f α φ fld).
  Qed.

  Lemma β__φ_normal_form_obj :
    forall schema ty qs flt,
      is_object_type schema ty ->
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (is_in_normal_form schema) (β__φ flt (normalize__φ schema ty qs)).
  Proof.
    apply (normalize_elim
             (fun schema ty q nq =>
                forall flt,
                  is_object_type schema ty ->
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  all (is_in_normal_form schema) (β__φ flt nq))
             (fun schema ty qs nqs =>
                forall flt,
                  is_object_type schema ty ->
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  all (is_in_normal_form schema) (β__φ flt nqs)));
      move=> schema //.
    all: do ?[by intros; simp β__φ; rewrite cats0;
              funelim (β__subqueryextract _ _)].
    all: do ?[by intros; rewrite Heq in H].

    all: do ?[by intros; rewrite Heq in H0].
        
    - intros; simp β__φ; rewrite cats0.
      funelim (β__subqueryextract _ _) => //.
      case: H3 => _ _ ->.
      move: H1; query_conforms; rewrite Heq2 => /and4P [_ _ _ Hqsc].
      move: H2; simp has_valid_fragments; rewrite Heq2 /= => Hv.
      by move: (normalize__φ_in_normal_form _ _ _ Hqsc Hv); are_in_normal_form.


    - intros; simp β__φ; rewrite cats0.
      funelim (β__subqueryextract _ _) => //.
      case: H3 => _ _ _ ->.
      move: H1; query_conforms; rewrite Heq1 => /and4P [_ _ _ Hqsc].
      move: H2; simp has_valid_fragments; rewrite Heq1 /= => Hv.
      by move: (normalize__φ_in_normal_form _ _ _ Hqsc Hv); are_in_normal_form.

    - intros.
      move: H1; query_conforms.
      move=> [_ _ _ Hqsc].
      move: H2; simp has_valid_fragments; rewrite Heq0 /= => /andP [/eqP Hty Hv].
      rewrite Hty in Hqsc.
        by apply: H.

    - intros; simp β__φ; rewrite cats0.
      funelim (β__subqueryextract _ _) => //.
      case: H3 => _ ->.
      move: H1; query_conforms; move=> [_ _ _ Hqsc].
      move: H2; simp has_valid_fragments; rewrite Heq1 /= => /andP [_ Hv].
      by move: (normalize__φ_in_normal_form _ _ _ Hqsc Hv); are_in_normal_form.

    - by intros; rewrite Heq0 in H0.

    - move=> ty hd tl IH IH' flt Hobj.
      all_cons=> [Hqc Hqsc].
      all_cons=> [Hv Hvs].
      rewrite β__φ_cat all_cat.
      by apply_andP; [apply: IH | apply: IH'].
  Qed.


  (*
  Ltac contr_scope_type s ty :=
    match goal with
    | [ H : is_object_type s ty, Hcontr : is_object_type s ty = false |- _ ] => rewrite H in Hcontr; inversion Hcontr
    end.
   *)

  
  Lemma β__φ_remove_redundancies_preserves_normal_form :
    forall schema ty qs flt,
    is_object_type schema ty ->
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    all (is_in_normal_form schema) (remove_redundancies (β__φ flt (normalize__φ schema ty qs))).
  Proof.
    apply (normalize_elim
             (fun schema ty q nq =>
                is_object_type schema ty ->
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                all (is_in_normal_form schema) (remove_redundancies nq))
             (fun schema ty qs nqs =>
                forall flt,
                  is_object_type schema ty ->
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  all (is_in_normal_form schema) (remove_redundancies (β__φ flt nqs))));
      move=> schema.
    all: do ?[by intros; rewrite Heq in H].

    - move=> ty f α φ Hcontr Hscope.
      by rewrite /query_conforms Hcontr.

    - move=> ty f fld α φ IH Hscope Hlook _ Hqc Hvc. simp remove_redundancies => /=.
      apply_andP.
      simp is_in_normal_form.
      apply_andP.
      move: Hqc; rewrite /query_conforms Hlook => /and4P [/orP [Hfobj | Habs] _ _ Hqsc];
      move: Hvc; simp has_valid_fragments; rewrite Hlook /= => Hv;
      simp β__φ; rewrite cats0.
      * orL; apply: remove_redundancies_preserves_all_fields => //.
        by apply: normalize__φ_in_object_scope_are_fields => //.

      * orR.
        apply: remove_redundancies_preserves_all_inlines => //.
        apply: normalize__φ_in_abstract_scope_are_inlines => //.

      simp β__φ; rewrite cats0.
      Abort.

        
  Lemma remove_redundancies_nf_all_normal_form :
    forall schema fty φ ty f α χ fld tl ,
    all (query_conforms schema ty) tl ->
    all (has_valid_fragments schema ty) tl ->
    query_conforms schema ty (NestedField f α φ) -> 
    is_object_type schema ty ->
    is_object_type schema fty ->
    lookup_field_in_type schema ty f = Some fld ->
    fld.(return_type).(tname) = fty ->
    all (is_in_normal_form schema)
        (remove_redundancies
           (normalize__φ schema fty φ ++ β__φ (NestedField f α χ) (normalize__φ schema ty tl))).
  Proof.
    apply (normalize_elim
             (fun schema fty q nq =>
                forall ty f α χ fld tl,
                all (query_conforms schema ty) tl ->
                all (has_valid_fragments schema ty) tl ->
                query_conforms schema ty (NestedField f α [:: q]) -> 
                is_object_type schema ty ->
                is_object_type schema fty ->
                lookup_field_in_type schema ty f = Some fld ->
                fld.(return_type).(tname) = fty ->
                all (is_in_normal_form schema)
                    (remove_redundancies
                       (nq ++ (β__φ (NestedField f α χ) (normalize__φ schema ty tl)))))
             (fun schema fty qs nqs =>
                forall ty f α χ fld tl,
                all (query_conforms schema ty) tl ->
                all (has_valid_fragments schema ty) tl ->
                query_conforms schema ty (NestedField f α qs) -> 
                is_object_type schema ty ->
                is_object_type schema fty ->
                lookup_field_in_type schema ty f = Some fld ->
                fld.(return_type).(tname) = fty ->
                all (is_in_normal_form schema)
                    (remove_redundancies
                       (nqs ++ β__φ (NestedField f α χ) (normalize__φ schema ty tl)))));
      move=> schema.
    Abort.
    
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

       * case: hd IH Hqc Hv; [move=> f α
                             | move=> l f α
                             | move=> f α φ
                             | move=> l f α φ
                             | move=> t φ];
         move=> IH Hqc Hv; simp normalize;
         rewrite ?Hobj /=; simp remove_redundancies.

         all: do ?[rewrite /are_in_normal_form; apply/andP; split=> //].
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
         move/nf_conformsP: Hqc2 => [fld Hlook H];
         rewrite Hlook /= Hobj /=; simp remove_redundancies.
         apply/andP; split=> //; last first.
         apply: filter_preserves_pred.
           by move: (IH' Hqsc Hvs); rewrite /are_in_normal_form => /andP [_].
         simp is_in_normal_form; apply/andP; split.
         move/and3P: H => [/orP [Hfobj | Hfabs] _ Hfqcs]; [orL | orR];                        
         move: Hv; simp has_valid_fragments; rewrite Hlook /= => Hfvs;
         move: Hfqcs; rewrite /queries_conform => /andP [_ Hfqcs];
         [apply: remove_redundancies_preserves_all_fields | apply: remove_redundancies_preserves_all_inlines];
         rewrite all_cat; apply/andP; split.
           by apply (normalize__φ_in_object_scope_are_fields _ _ _ Hfqcs Hfvs Hfobj).
           apply: β__φ_nf_fields => //. exact: Hlook. done.
           by apply (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hfqcs Hfvs Hfabs).
           apply: β__φ_nf_inlines => //. exact: Hlook. done.

           move: (IH Hqc Hv); simp normalize; rewrite Hlook /= Hobj /=.
           simp remove_redundancies => /=; simp β__φ; rewrite cats0; are_in_normal_form => _; rewrite all_seq1.
           simp is_in_normal_form => /andP [_ Hnf].


           funelim (β__φ _ _) => //.
              rewrite cats0.
              move: (IH Hqc Hv). are_in_normal_form=> [_]; simp normalize; rewrite Hlook /= Hobj /=.
              by simp remove_redundancies => /=; simp is_in_normal_form; simp β__φ; rewrite cats0 => /andP [/andP [_ Hnf] _].
              funelim (β__subqueryextract _ _) => //=.
              apply (H schema ty tl IH' Hqsc Hvs Hobj f0 α φ IH Hqc Hv fld Hlook H0).
              do ?[apply: (H schema ty tl IH' Hqsc Hvs Hobj f α φ IH Hqc Hv fld Hlook H0)].
         admit.
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

       + orR; apply: remove_redundancies_preserves_all_inlines.
         by rewrite all_cat; apply/andP; split;
           move/is_interface_is_abstract: Hintf => Habs;
           [ apply: normalize_in_abstract_scope_are_inlines
           | apply: normalize__φ_in_abstract_scope_are_inlines].

       +  admit.

       + orR; apply: remove_redundancies_preserves_all_inlines.
         by rewrite all_cat; apply/andP; split;
           move/is_union_is_abstract: Hunion => Habs;
           [ apply: normalize_in_abstract_scope_are_inlines
           | apply: normalize__φ_in_abstract_scope_are_inlines].

       + admit.
           

      
End QueryRewrite.

