From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap fset.
From Equations Require Import Equations.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Graph.
Require Import GraphAux.
Require Import GraphAuxLemmas.
Require Import GraphConformance.
Require Import GraphConformanceLemmas.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.
Require Import QueryConformanceLemmas.

Require Import Response.

Require Import NRGTNF.
Require Import NRGTNFLemmas.

Require Import QueryNormalization.
Require Import QueryNormalizationLemmas.

Require Import QuerySemantic.

Require Import SeqExtra.
Require Import QueryTactics.


Section Theory.
  Transparent qresponse_name has_response_name qname.
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  
  
  

  
  Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (fields _) _ = _ |- context [ (fields _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ ?u.(fields) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (u.(fields) _) => [ [v | vs] |] /=
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=
      | [ |- context [ _, _ ⊢ ⟦ _ ⟧ˢ in _ ] ] => simp execute_selection_set
      end.


  Variables (Name Vals : ordType) (s : @wfSchema Name Vals) (g : conformedGraph s).


  
  Lemma exec_frags_nil_func (f : Name -> seq (@Query Name Vals) -> seq Query) u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u = [::].
  Proof.
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Hunin.
    have /negbTE Hneq : u.(type) != t by move/memPn: Hunin => /(_ t (mem_head t ptys)); rewrite eq_sym.
    exec; rewrite /does_fragment_type_apply Hobj Hneq /=.
    apply: IH => //=.
    move: Hunin; rewrite /negb; case: ifP => //=.
      by case: ifP => //= Hin <- _; apply: mem_tail.
  Qed.

  Lemma exec_frags_nil u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u = [::].
  Proof.
      by apply: (exec_frags_nil_func (fun t qs => qs)).
  Qed.
  
  (* Lemma exec_frags_nil_get_types u ty φ : *)
  (*   u.(type) \notin get_possible_types s ty -> *)
  (*   ⟦ [seq InlineFragment t φ | t <- get_possible_types s ty] ⟧ˢ in u = [::]. *)
  (* Proof. *)
  (*     by move=> Hnin; apply: exec_frags_nil => //=; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object]. *)
  (* Qed. *)



  Lemma exec_cat_frags_func (f : Name -> seq (@Query Name Vals) -> seq Query) ptys u φ1 φ2 :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t (f t φ2) | t <- ptys] ⟧ˢ in u = s, g ⊢ ⟦ φ1 ⟧ˢ in u.   
  Proof.
    move=> Hfilterswap.
    move=> Hnin.
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n φ1 φ2 => /= [| n IH] φ1 φ2; first by rewrite leqn0 => /queries_size_0_nil ->; apply: exec_frags_nil_func.
    case: φ1 => //= [Hleq|q φ1]; first by apply: exec_frags_nil_func.
    have Hinlineswap : forall ptys rname φ, [seq InlineFragment t (filter_queries_with_label rname (f t φ)) | t <- ptys] =
                                       [seq InlineFragment t (f t (filter_queries_with_label rname φ)) | t <- ptys].
      by elim=> //= t' ptys' IH' rname φ; rewrite Hfilterswap IH'.
      
      
      case_query q; simp query_size => Hleq Hobj Hunin; exec;
                                        rewrite ?filter_queries_with_label_cat ?filter_map_inline_func ?Hinlineswap.
      all: do ? by congr cons; apply: IH; leq_queries_size.

    - case fld.(return_type) => //= rty.
      * case ohead => [v|] //=; rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        congr cons; congr pair; congr Response.Object.
          by rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

      * rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
          by congr cons; congr pair; congr Array.

    - by apply: IH; leq_queries_size.

    - case fld.(return_type) => //= rty.
      * case ohead => [v|] //=; rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        congr cons; congr pair; congr Response.Object.
          by rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
      * rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
          by congr cons; congr pair; congr Array.

    - by apply: IH; leq_queries_size.

    - by case: does_fragment_type_apply => //=; rewrite ?catA; apply: IH => //; leq_queries_size.
  Qed.
  
  Lemma exec_cat_frags ptys u φ1 φ2 :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- ptys] ⟧ˢ in u = s, g ⊢ ⟦ φ1 ⟧ˢ in u.                                                            
  Proof.
      by apply: (exec_cat_frags_func (fun t qs => qs)).
  Qed.

  Lemma exec_cat_frags_get_types ty u φ1 φ2 :
    u.(type) \notin get_possible_types s ty ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- get_possible_types s ty] ⟧ˢ in u =
                                                                          s, g ⊢ ⟦ φ1 ⟧ˢ in u.                                                                      
  Proof.
      by move=> Hnin; apply: exec_cat_frags => //; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.
  

  
  Lemma exec_inlined_func (f : Name -> seq (@Query Name Vals) -> seq Query) ptys u φ :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \in ptys ->
                 s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u =  s, g ⊢ ⟦ [:: InlineFragment u.(type) (f u.(type) φ) ] ⟧ˢ in u.
  Proof.
    move=> Hswap.
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj].
    rewrite inE => /orP [/eqP Heq | Hin].
    - rewrite -Heq in Hnin *; exec.
      have -> /= : does_fragment_type_apply s u.(type) u.(type).
        by apply: object_applies_to_itself; rewrite Heq; apply: Hobj.
          by rewrite cats0; apply: exec_cat_frags_func.
          
    - rewrite {1}execute_selection_set_equation_6.
      have -> /= : does_fragment_type_apply s u.(type) t = false.
      rewrite /does_fragment_type_apply.
      move/memPn: Hnin => /(_ u.(type) Hin) /negbTE.
        by rewrite Hobj /=.
          by apply: IH.
  Qed.
  
  Lemma exec_inlined ptys u φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \in ptys ->
                 s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u =  s, g ⊢ ⟦ [:: InlineFragment u.(type) φ ] ⟧ˢ in u.
  Proof.
      by apply: (exec_inlined_func (fun t qs => qs)).
  Qed.

  


  Lemma reground_exec φ u :
    u \in g.(nodes) ->
          s, g ⊢ ⟦ reground s u.(type) φ ⟧ˢ in u =  s, g ⊢ ⟦ φ ⟧ˢ in u.
  Proof.    
    funelim (reground s u.(type) φ) => //=; do ? by exec.
    all: do ? [by intros; exec; rewrite filter_reground_swap filter_filter_absorb // H].
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty| rty] /=.
      * case Hv : ohead => [v|] //=;
                               rewrite filter_reground_swap filter_filter_absorb // H0 // -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        congr cons; congr pair; congr Response.Object.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbours_are_in_nodes.
          have Hvtype : v.(type) = rty.
          rewrite Hrty /= in Heq.
          apply: (in_object_possible_types Heq).
          have Hlook : lookup_field_in_type s u.(type) (Field response_name1 arguments1) = Some f by [].
          move/ohead_in: Hv => Hin.
          move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name1 arguments1) f Hlook v Hin).
            by rewrite Hrty.
              by apply: H => //; rewrite Hvtype.
              
              
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        have Hvin : v \in g.(nodes).
        apply: neighbours_are_in_nodes; exact: Hin.
        have Hvtype : v.(type) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field response_name1 arguments1) = Some f by [].
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name1 arguments1) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
            by apply: H => //; rewrite Hvtype.
            
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty | rty] //=.
      * case Hv : ohead => [v|] /=; rewrite filter_reground_swap filter_filter_absorb // H0 //.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Response.Object.
        rewrite exec_inlined_func //.
        exec.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
          by apply/allP; apply: neighbours_are_in_nodes.
          have Hvobj := (node_in_graph_has_object_type Hvin).
          have -> /= : does_fragment_type_apply s v.(type) v.(type) by apply: object_applies_to_itself.
          rewrite cats0.
            by apply: H.
            
              by apply: filter_reground_swap.
                by apply: uniq_get_possible_types.
                  by apply/allP; apply: in_possible_types_is_object.

                  move/ohead_in: Hv => Hin.
                  move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name1 arguments1) f Heq0 v Hin).
                    by rewrite Hrty.
                    
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
        exec.
        have Hvin : v \in g.(nodes) by apply: neighbours_are_in_nodes; exact: Hin.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(type) v.(type) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
            by apply: filter_reground_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.  

                move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name1 arguments1) f Heq0 v Hin).
                  by rewrite Hrty.
                  

    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty| rty] /=.
      * case Hv : ohead => [v|] //=;
                               rewrite filter_reground_swap filter_filter_absorb // H0 // -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        congr cons; congr pair; congr Response.Object.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbours_are_in_nodes.
          have Hvtype : v.(type) = rty.
          rewrite Hrty /= in Heq.
          apply: (in_object_possible_types Heq).
          have Hlook : lookup_field_in_type s u.(type) (Field response_name2 arguments2) = Some f by [].
          move/ohead_in: Hv => Hin.
          move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name2 arguments2) f Hlook v Hin).
            by rewrite Hrty.
              by apply: H => //; rewrite Hvtype.
              
              
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        have Hvin : v \in g.(nodes).
        apply: neighbours_are_in_nodes; exact: Hin.
        have Hvtype : v.(type) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field response_name2 arguments2) = Some f by [].
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name2 arguments2) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
            by apply: H => //; rewrite Hvtype.
            
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty | rty] //=.
      * case Hv : ohead => [v|] /=; rewrite filter_reground_swap filter_filter_absorb // H0 //.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Response.Object.
        rewrite exec_inlined_func //.
        exec.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
          by apply/allP; apply: neighbours_are_in_nodes.
          have Hvobj := (node_in_graph_has_object_type Hvin).
          have -> /= : does_fragment_type_apply s v.(type) v.(type) by apply: object_applies_to_itself.
          rewrite cats0.
            by apply: H.
            
              by apply: filter_reground_swap.
                by apply: uniq_get_possible_types.
                  by apply/allP; apply: in_possible_types_is_object.

                  move/ohead_in: Hv => Hin.
                  move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name2 arguments2) f Heq0 v Hin).
                    by rewrite Hrty.


      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
        exec.
        have Hvin : v \in g.(nodes) by apply: neighbours_are_in_nodes; exact: Hin.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(type) v.(type) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
            by apply: filter_reground_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.  

                move: (@neighbours_are_subtype_of_field Name Vals s g u (Field response_name2 arguments2) f Heq0 v Hin).
                  by rewrite Hrty.
  Qed.

  
  Theorem normalize_queries_exec ty φ u :
    u \in g.(nodes) ->
          u.(type) \in get_possible_types s ty ->
                       s, g ⊢ ⟦ ground_queries s ty φ ⟧ˢ in u = s, g ⊢ ⟦ φ ⟧ˢ in u.
  Proof.
    funelim (ground_queries s ty φ) => //= Huin Hin.
    - by have <- /= := (in_object_possible_types Heq Hin); apply: reground_exec.
    - have -> /= :
        s, g ⊢ ⟦ [seq InlineFragment t (reground s t queries) | t <- get_possible_types s type_in_scope] ⟧ˢ in u =
        s, g ⊢ ⟦ [:: InlineFragment u.(type) (reground s u.(type) queries)] ⟧ˢ in u.
      apply: exec_inlined_func => //=.
        by apply: filter_reground_swap.
          by apply: uniq_get_possible_types.
            by apply/allP; apply: in_possible_types_is_object.
            
            exec.
            have -> /= : does_fragment_type_apply s u.(type) u.(type)
              by apply: object_applies_to_itself; apply: (in_possible_types_is_object Hin).
            rewrite cats0.
              by apply: reground_exec.
  Qed.


  Lemma normalize_root_query_is_in_normal_form φ :
    queries_conform s s.(query_type) φ ->
    NRGTNF.are_non_redundant (reground s s.(query_type) φ) /\
    are_grounded s (reground s s.(query_type) φ).
  Proof.
    intros; split.
    - by apply: reground_are_non_redundant; apply: query_has_object_type.
    - apply: are_grounded2_are_grounded.
        by apply: reground_are_grounded2; apply: query_has_object_type.
  Qed.
  
  
  Theorem exec_normalize_from_root φ :
    queries_conform s s.(query_type) φ ->
    s, g ⊢ ⟦ ground_queries s s.(query_type) φ ⟧ˢ in g.(root) = s, g ⊢ ⟦ φ ⟧ˢ in g.(root).
  Proof.
    intros; apply: normalize_queries_exec.
    - by apply: root_in_nodes.
    - have -> /= := (root_query_type g).
      have Hobj := (query_has_object_type s).
        by rewrite get_possible_types_objectE //= mem_seq1; apply/eqP.
  Qed.





  (* Section Equiv. *)
    
  (*   Ltac equiv := *)
  (*     repeat match goal with *)
  (*            | [ H: ?eq1 && ?eq2 = _ |- context [_ && _]] => rewrite H /= *)
  (*            | [ H: lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _ ]] => rewrite H /= *)
  (*            | [ H:  does_fragment_type_apply _ _ _ = _ |- context [does_fragment_type_apply _ _ _]] => *)
  (*              rewrite H /= *)
  (*            | [ H:  is_true (does_fragment_type_apply _ _ _) |- context [does_fragment_type_apply _ _ _]] => *)
  (*              rewrite H /= *)
  (*            | [|- context [ Equiv _ _ _ ]] => simp Equiv *)
  (*            end. *)
    
    
  (*   Lemma equiv_eval1 ty φ1 φ2 : *)
  (*     (forall t, t \in get_possible_types s ty -> *)
  (*                 t ⊢ φ1 ≡ φ2) -> *)
  (*     forall u, u.(type) \in get_possible_types s ty -> *)
  (*                       ⟦ φ1 ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u. *)
  (*   Proof. *)
  (*     move=> Heq u Hin. *)
  (*     move: (Heq _ Hin). *)
  (*     funelim (Equiv _  φ1 φ2) => //=. *)
  (*   Qed. *)

  (* End Equiv. *)


  
  
  (* Theorem execs_on_nrgtnf_are_equivalent u φ : *)
  (*   are_in_normal_form s φ -> *)
  (*   are_non_redundant φ -> *)
  (*   ⦃ φ in u ⦄ = ⟦ φ in u ⟧ˢ. *)
  (* Proof. *)
  (*   move: {2}(queries_size _) (leqnn (queries_size φ)) => n. *)
  (*   elim: n φ u => [| n IH] φ u. *)
  (*   - by rewrite leqn0 => /queries_size_0_nil ->.  *)
  (*   - case: φ => //=; case=> /= [f α | l f α | f α φ | l f α φ | t φ] qs Hleq. *)
  (*     * simp are_in_normal_form => /andP [Hflds Hnf]. *)
  (*       simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr]. *)
  (*       simp execute_selection_set; simp execute_selection_set2. *)
  (*       case: (u.(fields) _) => //=; [case=> // v|]; *)
  (*                                rewrite (filter_not_similar_preserves_list (SingleField f α)) // IH //; by apply: asdf. *)
        
  (*     * simp are_in_normal_form => /andP [Hflds Hnf]. *)
  (*       simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr]. *)
  (*       simp execute_selection_set; simp execute_selection_set2. *)
  (*       case: (u.(fields) _) => //=; [case=> // v|]; *)
  (*                                rewrite (filter_not_similar_preserves_list (LabeledField l f α)) // IH //; by apply: asdf. *)

        
  (*     * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs]. *)
  (*       simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].  *)
  (*       simp execute_selection_set; simp execute_selection_set2. *)
  (*       case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //. *)
  (*       case: fld Hlook => f' args; case=> ty Hlook /=.  *)
  (*     + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //. *)
  (*       rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*           by rewrite IH //; ssromega. *)
            
  (*     + rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.  *)
  (*       congr cons; last by apply: IH => //; ssromega. *)
  (*       congr pair; congr Array. *)
  (*       apply/eq_in_map => v Hin. *)
  (*       rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*     + by rewrite IH //; ssromega. *)
        
  (*       * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs]. *)
  (*         simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].  *)
  (*         simp execute_selection_set; simp execute_selection_set2. *)
  (*         case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. *)
  (*         case: fld Hlook => f' args; case=> ty Hlook /=.  *)
  (*     + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. *)
  (*       rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*           by rewrite IH //; ssromega. *)
            
  (*     + rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.  *)
  (*       congr cons; last by apply: IH => //; ssromega. *)
  (*       congr pair; congr Array. *)
  (*       apply/eq_in_map => v Hin. *)
  (*       rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*     + by rewrite IH //; ssromega.  *)

  (*       * simp are_in_normal_form => /and5P [Hobj Hflds Hnf Hinl Hnfs]. *)
  (*         simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. *)
  (*         simp execute_selection_set; simp execute_selection_set2. *)
  (*         case Hfrag: does_fragment_type_apply => //=; last by apply: IH => //; ssromega. *)
  (*         rewrite execute_selection_set2_cat. *)
  (*         rewrite (all_invalid_fragments_eval u φ qs) // ?cats0; last first. *)
  (*         rewrite /does_fragment_type_apply Hobj in Hfrag. *)
  (*           by move/eqP in Hfrag; rewrite Hfrag.         *)
            
            
  (*           rewrite all_invalid_fragments_exec //; [apply: IH => //; rewrite -/(queries_size φ) in Hleq; ssromega|]. *)
  (*           rewrite /does_fragment_type_apply Hobj in Hfrag. *)
  (*             by move/eqP in Hfrag; rewrite Hfrag. *)
  (* Qed. *)
  

End Theory.