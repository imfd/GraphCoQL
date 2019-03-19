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
        | false | false :=
            (* abstract type in scope & guard has abstract type *)
            let possible_types := get_possible_types schema t in
            let scope_possible_types := get_possible_types schema type_in_scope in
            let intersection := (scope_possible_types :&: possible_types)%fset in
            [seq (InlineFragment ty (normalize__φ schema  ty φ)) | ty <- intersection]
            
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


  Lemma normalize_in_normal_form schema query :
    forall type_in_scope,
      query_conforms schema type_in_scope query ->
      has_valid_fragments schema type_in_scope query ->
      are_in_normal_form schema (normalize schema type_in_scope query).
  Proof.
    elim query using Query_ind with
        (Pl := fun queries =>
                forall type_in_scope,
                   all (query_conforms schema type_in_scope) queries ->
                   all (has_valid_fragments schema type_in_scope) queries ->
                   are_in_normal_form schema (normalize__φ schema type_in_scope queries)) => //.
    - move=> f α ty Hqc Hv.
      simp normalize; case is_object_type => /=.
      * apply/andP; split => //; apply: H.
      * rewrite /are_in_normal_form.
        apply/andP; split.
        apply/orP; right. apply/allP=> x /mapP [t Hin ->] /=.
        by simp is_inline_fragment.
        apply/allP => x /mapP [t Hpty ->].
        rewrite is_in_normal_form_equation_5.
        apply/and3P; split => //=.
        move: (type_in_scope_N_scalar_enum Hqc) => [Hobj | Hintf | Hunion].
      + by move/(in_object_possible_types Hobj): Hpty => ->. 
      + rewrite (get_possible_types_interfaceE Hintf) in Hpty.
        by apply: (in_implementation_is_object Hpty).
      + rewrite (get_possible_types_unionE Hunion) in Hpty.
          by apply: (in_union_is_object Hpty).
    - move=> l f α ty Hqc Hv.
      simp normalize; case is_object_type => /=.
      * apply/andP; split => //; apply: H.
      * rewrite /are_in_normal_form.
        apply/andP; split.
        apply/orP; right. apply/allP=> x /mapP [t Hin ->] /=.
          by simp is_inline_fragment.
        apply/allP => x /mapP [t Hpty ->].
        rewrite is_in_normal_form_equation_5.
        apply/and3P; split => //=.
        move: (type_in_scope_N_scalar_enum Hqc) => [Hobj | Hintf | Hunion].
      + by move/(in_object_possible_types Hobj): Hpty => ->. 
      + rewrite (get_possible_types_interfaceE Hintf) in Hpty.
        by apply: (in_implementation_is_object Hpty).
      + rewrite (get_possible_types_unionE Hunion) in Hpty.
          by apply: (in_union_is_object Hpty).

    - move=> f α φ IH ty Hqc Hv.
      set Hqc' := Hqc.
      simp normalize; case Hlook: lookup_field_type => [rty|] //=.
      move/nf_conformsP: Hqc' => [fld Hlook' /and3P [_ _ H]].
      move: (lookup_field_or_type Hlook' Hlook) => Heq.
      move: Hv; simp has_valid_fragments; rewrite Hlook /= => Hvals.
      rewrite Heq in Hvals *.
      case Hobj : is_object_type => /=.
      * rewrite /are_in_normal_form /=; apply/andP; split=> //=.
        apply/andP; split=> //.
        simp is_in_normal_form.
        rewrite -/(are_in_normal_form _ _).
        apply: IH => //.
          by rewrite /queries_conform in H; move/andP: H => [_ H].
      * rewrite /are_in_normal_form; apply/andP; split.
        + apply/orP; right.
          by apply/allP => x /mapP [t Hin ->]; program_simpl.
        + apply/allP=> x /mapP [t Hin ->]; simp is_in_normal_form.
          move: (type_in_scope_N_scalar_enum Hqc) => [Hobj' | Hintf | Hunion].
          (* Obj *)
            by rewrite Hobj in Hobj'.
          (* Intf *)
          rewrite (get_possible_types_interfaceE Hintf) in Hin.
          apply/and3P; split=> //.
            by apply: (in_implementation_is_object Hin).
            rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by rewrite /queries_conform in H; move/andP: H => [_ H].
          (* Union *)
          rewrite (get_possible_types_unionE Hunion) in Hin.     
          move/in_union_is_object: Hin => Hobj'.
          apply/and3P; split=> //.
          rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by rewrite /queries_conform in H; move/andP: H => [_ H].
    -  move=> l f α φ IH ty Hqc Hv.
      set Hqc' := Hqc.
      simp normalize; case Hlook: lookup_field_type => [rty|] //=.
      move/nf_conformsP: Hqc' => [fld Hlook' /and3P [_ _ H]].
      move: (lookup_field_or_type Hlook' Hlook) => Heq.
      move: Hv; simp has_valid_fragments; rewrite Hlook /= => Hvals.
      rewrite Heq in Hvals *.
      case Hobj : is_object_type => /=.
      * rewrite /are_in_normal_form /=; apply/andP; split=> //=.
        apply/andP; split=> //.
        simp is_in_normal_form.
        rewrite -/(are_in_normal_form _ _).
        apply: IH => //.
          by rewrite /queries_conform in H; move/andP: H => [_ H].
      * rewrite /are_in_normal_form; apply/andP; split.
        + apply/orP; right.
          by apply/allP => x /mapP [t Hin ->]; program_simpl.
        + apply/allP=> x /mapP [t Hin ->]; simp is_in_normal_form.
          move: (type_in_scope_N_scalar_enum Hqc) => [Hobj' | Hintf | Hunion].
          (* Obj *)
            by rewrite Hobj in Hobj'.
          (* Intf *)
          rewrite (get_possible_types_interfaceE Hintf) in Hin.
          apply/and3P; split=> //.
            by apply: (in_implementation_is_object Hin).
            rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by rewrite /queries_conform in H; move/andP: H => [_ H].
          (* Union *)
          rewrite (get_possible_types_unionE Hunion) in Hin.     
          move/in_union_is_object: Hin => Hobj'.
          apply/and3P; split=> //.
          rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by rewrite /queries_conform in H; move/andP: H => [_ H].
    - move=> t φ IH ty Hqc Hv.
      simp normalize; case Hobj: is_object_type => //=.
      rewrite /are_in_normal_form; apply/andP; split.
      * simp normalize; case Hobj: is_object_type => /=.
        apply/orP; right => /=.
        simp

              
End QueryRewrite.

