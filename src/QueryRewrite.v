Require Import List Relations Lia.

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

Section QueryRewrite.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Notation is_field := (@QueryAux.is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).



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
          by apply/allP => x /mapP [t Hin ->]; program_simpl.
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
          by apply/allP => x /mapP [t Hin ->]; program_simpl.
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


  

         
End QueryRewrite.

