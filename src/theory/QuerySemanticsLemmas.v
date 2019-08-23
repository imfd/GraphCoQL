From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Base.
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


Require Import SeqExtra.
Require Import QueryTactics.
Require Import GeneralTactics.

Require Import QuerySemantic.

Section Theory.
  Transparent qresponse_name has_response_name.
  

  
  Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (field_seq_value (nfields _) _) = _ |- context [ field_seq_value (nfields _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ field_seq_value ?u.(nfields) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (field_seq_value u.(nfields) _) => [ [v | vs] |] /=

      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [|- context[ execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=

      | [|- context [execute_selection_set_unfold_clause_6 _ _ _ _ _ (does_fragment_type_apply _ _ _)] ] =>
        let Hfapplies := fresh "Hfapplies" in
        case Hfapplies : does_fragment_type_apply => //=
   
      | [ |- context [ _, _ ⊢ ⟦ _ ⟧ˢ in _ ] ] => simp execute_selection_set
      end.

  Ltac exec2 :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (field_seq_value (nfields _) _) = _ |- context [ field_seq_value (nfields _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ field_seq_value ?u.(nfields) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (field_seq_value u.(nfields) _) => [ [v | vs] |] /=

      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [|- context[ execute_selection_set2_unfold_clause_4_clause_1 _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set2_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [|- context[ execute_selection_set2_unfold_clause_5_clause_1 _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set2_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [H : (ohead (neighbours_with_field _ _ _)) = _ |- context [ ohead (neighbours_with_field _ _ _)] ] =>
        rewrite H /=
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=
      | [ |- context [ _, _ ⊢ ≪ _ ≫ in _ ] ] => simp execute_selection_set2
      end.


  Variables (Vals : eqType) (s : @wfGraphQLSchema Vals) (g : conformedGraph s).


  
  Lemma exec_frags_nil_func (f : Name -> seq (@Query Vals) -> seq Query) u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u = [::].
  Proof.
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Hunin.
    have /negbTE Hneq : u.(ntype) != t by move/memPn: Hunin => /(_ t (mem_head t ptys)); rewrite eq_sym.
    simp execute_selection_set; rewrite /does_fragment_type_apply Hobj Hneq /=.
    apply: IH => //=.
    move: Hunin; rewrite /negb; case: ifP => //=.
      by case: ifP => //= Hin <- _; apply: mem_tail.
  Qed.

  Lemma exec_frags_nil u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u = [::].
  Proof.
      by apply: (exec_frags_nil_func (fun t qs => qs)).
  Qed.
 

  Lemma exec_cat_frags_func (f : Name -> seq (@Query Vals) -> seq Query) ptys u φ1 φ2 :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
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
                                        rewrite ?filter_queries_with_label_cat ?filter_map_inline_func ?Hinlineswap ?IH //; leq_queries_size.
      (* all: do ? by congr cons; apply: IH; leq_queries_size. *)

    - by congr cons; congr pair; congr Response.Object; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
        
    - by congr cons; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by congr cons; congr pair; congr Response.Object; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by congr cons; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by rewrite catA; apply: IH => //; leq_queries_size.
  Qed.
  
  Lemma exec_cat_frags ptys u φ1 φ2 :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- ptys] ⟧ˢ in u = s, g ⊢ ⟦ φ1 ⟧ˢ in u.                                                            
  Proof.
      by apply: (exec_cat_frags_func (fun t qs => qs)).
  Qed.

  Lemma exec_cat_frags_get_types ty u φ1 φ2 :
    u.(ntype) \notin get_possible_types s ty ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- get_possible_types s ty] ⟧ˢ in u =
                                                                          s, g ⊢ ⟦ φ1 ⟧ˢ in u.                                                                      
  Proof.
      by move=> Hnin; apply: exec_cat_frags => //; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.
  

  
  Lemma exec_inlined_func (f : Name -> seq (@Query Vals) -> seq Query) ptys u φ :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \in ptys ->
                 s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u =  s, g ⊢ ⟦ [:: InlineFragment u.(ntype) (f u.(ntype) φ) ] ⟧ˢ in u.
  Proof.
    move=> Hswap.
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj].
    rewrite inE => /orP [/eqP Heq | Hin].
    - rewrite -Heq in Hnin *; simp execute_selection_set.
      have -> /= : does_fragment_type_apply s u.(ntype) u.(ntype).
        by apply: object_applies_to_itself; rewrite Heq; apply: Hobj.
          by rewrite cats0; apply: exec_cat_frags_func.
          
    - rewrite {1}execute_selection_set_equation_6.
      have -> /= : does_fragment_type_apply s u.(ntype) t = false.
      rewrite /does_fragment_type_apply.
      move/memPn: Hnin => /(_ u.(ntype) Hin) /negbTE.
        by rewrite Hobj /=.
          by apply: IH.
  Qed.
  
  Lemma exec_inlined ptys u φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \in ptys ->
                 s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u =  s, g ⊢ ⟦ [:: InlineFragment u.(ntype) φ ] ⟧ˢ in u.
  Proof.
      by apply: (exec_inlined_func (fun t qs => qs)).
  Qed.

  

  (**
     This lemma states that normalizing a query with the same type as 
     the node where it is being evaluated, preserves its semantics.
   *)
  Lemma normalize_exec φ u :
    u \in g.(nodes) ->
          s, g ⊢ ⟦ normalize s u.(ntype) φ ⟧ˢ in u =  s, g ⊢ ⟦ φ ⟧ˢ in u.
  Proof.    
    funelim (normalize s u.(ntype) φ) => //=; do ? by exec.
    all: do ? [by intros; exec; rewrite filter_normalize_swap filter_filter_absorb // H]; exec => Huin.

    all: do ? [rewrite filter_normalize_swap filter_filter_absorb // H0 // -?filter_normalize_swap find_queries_filter_nil].
    - simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      congr cons; congr pair; congr Response.Object.
      have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbours_are_in_nodes.
      have Hvtype : v.(ntype) = rty.
        rewrite Hrty /= in Heq.
        apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(ntype) (Field name1 arguments1) = Some f by [].
        move/ohead_in: Hv => Hin.
        move: (@neighbours_are_subtype_of_field Vals s g u (Field name1 arguments1) f Hlook v Hin).
          by rewrite Hrty.
      by apply: H => //; rewrite Hvtype.
      
    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      have Hvin : v \in g.(nodes).
        apply: neighbours_are_in_nodes; exact: Hin.
      have Hvtype : v.(ntype) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(ntype) (Field name1 arguments1) = Some f by [].
        move: (@neighbours_are_subtype_of_field Vals s g u (Field name1 arguments1) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
      by apply: H => //; rewrite Hvtype.
            
    - simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Response.Object.
        rewrite exec_inlined_func //.
        simp execute_selection_set.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
          by apply/allP; apply: neighbours_are_in_nodes.
          have Hvobj := (node_in_graph_has_object_type Hvin).
          have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
          rewrite cats0.
            by apply: H.
            
              by apply: filter_normalize_swap.
                by apply: uniq_get_possible_types.
                  by apply/allP; apply: in_possible_types_is_object.

                  move/ohead_in: Hv => Hin.
                  move: (@neighbours_are_subtype_of_field Vals s g u (Field name1 arguments1) f Heq0 v Hin).
                    by rewrite Hrty.
                    
      * congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
        simp execute_selection_set.
        have Hvin : v \in g.(nodes) by apply: neighbours_are_in_nodes; exact: Hin.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
            by apply: filter_normalize_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.  

                move: (@neighbours_are_subtype_of_field Vals s g u (Field name1 arguments1) f Heq0 v Hin).
                  by rewrite Hrty.
                  

    - simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      congr cons; congr pair; congr Response.Object.
      have Hvin : v \in g.(nodes).
      apply: ohead_in_nodes; last by apply: Hv.
      apply/allP.
        by apply: neighbours_are_in_nodes.
      have Hvtype : v.(ntype) = rty.
      rewrite Hrty /= in Heq.
      apply: (in_object_possible_types Heq).
      have Hlook : lookup_field_in_type s u.(ntype) (Field name2 arguments2) = Some f by [].
      move/ohead_in: Hv => Hin.
      move: (@neighbours_are_subtype_of_field Vals s g u (Field name2 arguments2) f Hlook v Hin).
        by rewrite Hrty.
          by apply: H => //; rewrite Hvtype.
              
              
    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      have Hvin : v \in g.(nodes).
      apply: neighbours_are_in_nodes; exact: Hin.
      have Hvtype : v.(ntype) = rty.
      rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
      have Hlook : lookup_field_in_type s u.(ntype) (Field name2 arguments2) = Some f by [].
      move: (@neighbours_are_subtype_of_field Vals s g u (Field name2 arguments2) f Hlook v Hin).
        by rewrite Hrty /=. (* ?? *)
          by apply: H => //; rewrite Hvtype.
            
    - simp merge_selection_sets => /=; rewrite cats0.
      congr cons; congr pair; congr Response.Object.
      rewrite exec_inlined_func //.
      simp execute_selection_set.
      have Hvin : v \in g.(nodes).
      apply: ohead_in_nodes; last by apply: Hv.
        by apply/allP; apply: neighbours_are_in_nodes.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
          
            by apply: filter_normalize_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.
                
                move/ohead_in: Hv => Hin.
                move: (@neighbours_are_subtype_of_field Vals s g u (Field name2 arguments2) f Heq0 v Hin).
                  by rewrite Hrty.
                  

    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
      simp execute_selection_set.
      have Hvin : v \in g.(nodes) by apply: neighbours_are_in_nodes; exact: Hin.
      have Hvobj := (node_in_graph_has_object_type Hvin).
      have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
      rewrite cats0.
        by apply: H.
          by apply: filter_normalize_swap.
            by apply: uniq_get_possible_types.
              by apply/allP; apply: in_possible_types_is_object.  
              
              move: (@neighbours_are_subtype_of_field Vals s g u (Field name2 arguments2) f Heq0 v Hin).
                by rewrite Hrty.
  Qed.



  (**
     This theorem states that [normalize_queries] preserves the semantics of the query,
     if the node's type where the query is executed is subtype of the type used 
     to normalize.
   *)
  Theorem normalize_queries_exec ty φ u :
    u \in g.(nodes) ->
          u.(ntype) \in get_possible_types s ty ->
                       s, g ⊢ ⟦ normalize_queries s ty φ ⟧ˢ in u = s, g ⊢ ⟦ φ ⟧ˢ in u.
  Proof.
    funelim (normalize_queries s ty φ) => //= Huin Hin.
    - by have <- /= := (in_object_possible_types Heq Hin); apply: normalize_exec.
    - have -> /= :
        s, g ⊢ ⟦ [seq InlineFragment t (normalize s t queries) | t <- get_possible_types s type_in_scope] ⟧ˢ in u =
        s, g ⊢ ⟦ [:: InlineFragment u.(ntype) (normalize s u.(ntype) queries)] ⟧ˢ in u.
      apply: exec_inlined_func => //=.
        by apply: filter_normalize_swap.
          by apply: uniq_get_possible_types.
            by apply/allP; apply: in_possible_types_is_object.
            
            simp execute_selection_set.
            have -> /= : does_fragment_type_apply s u.(ntype) u.(ntype)
              by apply: object_applies_to_itself; apply: (in_possible_types_is_object Hin).
            rewrite cats0.
              by apply: normalize_exec.
  Qed.


  (**
     This lemma states that if a query conforms to the Query type, then 
     normalizing results in a query in normal form.
   *)
  (* Conformance is not really needed... *)
  Lemma normalize_root_query_is_in_normal_form φ :
    queries_conform s s.(query_type) φ ->
    NRGTNF.are_non_redundant (normalize s s.(query_type) φ) /\
    are_grounded s (normalize s s.(query_type) φ).
  Proof.
    intros; split.
    - by apply: normalize_are_non_redundant; apply: query_has_object_type.
    - apply: are_grounded2_are_grounded.
        by apply: normalize_are_grounded2; apply: query_has_object_type.
  Qed.
  
  (**
     This theorem states that if a query conforms to the Query type, 
     then normalizing it with the Query type preserves its semantics,
     whenever evaluated on the root node of the graph.
   *)
  Theorem exec_normalize_from_root φ :
    queries_conform s s.(query_type) φ ->
    s, g ⊢ ⟦ normalize_queries s s.(query_type) φ ⟧ˢ in g.(root) = s, g ⊢ ⟦ φ ⟧ˢ in g.(root).
  Proof.
    intros; apply: normalize_queries_exec.
    - by apply: root_in_nodes.
    - have -> /= := (root_query_type g).
      have Hobj := (query_has_object_type s).
        by rewrite get_possible_types_objectE //= mem_seq1; apply/eqP.
  Qed.


  
  Transparent is_field.

  (**
     This lemma states that [execute_selection_set2] distributes over list concatenation.
   *)
  Lemma exec2_cat u φ β :
    s, g ⊢ ≪ φ ++ β ≫ in u = s, g ⊢ ≪ φ ≫ in u ++ s, g ⊢ ≪ β ≫ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ β => /= [| n IH] φ β; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => // q φ; case_query q; simp query_size => Hleq; exec2; rewrite -/cat ?IH //; leq_queries_size.
      by case does_fragment_type_apply => /=; rewrite ?catA; apply: IH; leq_queries_size.
  Qed.


  

  (**
     This lemma states that evaluating a list of inline fragments in which 
     all have a type condition that does not apply to the node's type will result 
     in an empty response ([execute_selection_set2]).
   *)
  Lemma exec_inlines_nil φ u :
    all (fun q => q.(is_inline_fragment)) φ ->
     all (fun q => if q is on t { _ } then
                 ~~ does_fragment_type_apply s u.(ntype) t
               else
                 true) φ ->
    s, g ⊢ ⟦ φ ⟧ˢ in u = [::].
  Proof.
    funelim (s, g ⊢ ⟦ φ ⟧ˢ in u) => //=; bcase.
      by rewrite Heq in Hb0.
    by apply: H => //; intros; apply: (Hnappl q) => //; apply: mem_tail.
  Qed.

 
  (**
     This lemma states that evaluating a list of inline fragments in which 
     all have a type condition that does not apply to the node's type will result 
     in an empty response ([execute_selection_set2]).
   *)
  Lemma exec2_inlines_nil φ u :
    all (fun q => q.(is_inline_fragment)) φ ->
    all (fun q => if q is on t { _ } then
                 ~~ does_fragment_type_apply s u.(ntype) t
               else
                 true) φ ->
    s, g ⊢ ≪ φ ≫ in u = [::].
  Proof.
    funelim (s, g ⊢ ≪ φ ≫ in u) => //=; bcase.
      by rewrite Heq in Hb0.
    by apply: H => //; intros; apply: (Hnappl q) => //; apply: mem_tail.
  Qed.
  
 

  (**
     This lemma states that evaluating a concatenation of two lists [φ] and [β], 
     where [β] consists of inline fragments whose type condition does not apply 
     to the node's type, is equal to just evaluatin [φ] by itself ([β] does 
     not produce any response).

     I believe this could be extended to any type of list [β], if we include 
     the notion of query conformance.

     See also:
     - [exec_equivalence]
   *)
  Lemma exec_grounded_inlines_nil φ β u :
    all (fun q => q.(is_inline_fragment)) β ->
    all (fun q => if q is on t { _ } then
                 ~~ does_fragment_type_apply s u.(ntype) t
               else
                 true) β ->
    s, g ⊢ ⟦ φ ++ β ⟧ˢ in u = s, g ⊢  ⟦ φ ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ β u => /= [| n IH] φ β u; first by rewrite leqn0 => /queries_size_0_nil -> /=; apply: exec_inlines_nil.
    case: φ => //= [_ | q φ]; first by apply: exec_inlines_nil.
    case_query q; simp query_size => Hleq; intros; exec; rewrite ?filter_queries_with_label_cat ?find_queries_with_label_cat ?[find_queries_with_label _ _ _ β]find_fragment_not_applies_is_nil // ?cats0 //.
    all: do ? congr cons.
    all: do ? [apply: IH => //; leq_queries_size].
    all: do ? by apply: filter_preserves_inlines.
    all: do ? by apply: filter_preserves_fragment_not_applies.

    - by rewrite catA; apply: IH; leq_queries_size.
  Qed.   


  (**
     This lemma states that if there is no grounded fragment with type condition 
     [ty], then no fragment applies to [ty].

     The idea is that grounded fragments have Object types as type condition and 
     the only way for an Object type to apply to another is that they are the same.
     
     See also:
     - [exec_equivalence]
   *)
  Lemma find_frags_nil_then_N_applies φ ty :
    find_fragment_with_type_condition ty φ = [::] ->
    are_grounded_inlines s φ ->
    all (fun q => if q is on t { _ } then
                 ~~ does_fragment_type_apply s ty t
               else
                 true) φ.
  Proof.
    elim: φ => // q φ IH; case_query q => //.
    simp find_fragment_with_type_condition; case: eqP => //= /eqP Hneq Hfind.
    simp is_grounded; bcase.
    move: Hb2; bcase.
    rewrite /does_fragment_type_apply Hb0 Hneq.
    apply_andP; by apply: IH.
  Qed.
    
      
  (**
     This theorem states that in the presence of a query in normal form, 
     both the semantics with collection and the simplified semantics are 
     equivalent.

     ---- 
     See also :
     - [execute_selection_set]
     - [execute_selection_set2]
     
   *)
  Theorem exec_equivalence u φ :
    are_grounded s φ ->
    are_non_redundant φ -> 
    s, g ⊢ ⟦ φ ⟧ˢ in u = s, g ⊢ ≪ φ ≫ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => /= [| n IH] φ u; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => // q φ; case_query q; simp query_size => Hleq; grounding; non_red => /=; bcase; exec; exec2.

    all: do ?[by apply: IH => //=; grounding].
    
    all: do ? [rewrite filter_find_fields_nil_is_nil in IH *; [
               | by move: Hb2; rewrite are_grounded_fields_E; bcase
               | by apply/eqP ] ].
    all: do ? congr cons.
    all: do ? [by apply: IH; leq_queries_size; [grounding | non_red] ].     

    all: do ? [congr pair; congr Array; apply/eq_in_map=> v Hin; congr Response.Object].
    all: do ? [rewrite find_queries_nil_if_find_fields_nil// /merge_selection_sets /= ?cats0 in IH *; last by apply/eqP].
    all: do ? by rewrite IH //; leq_queries_size.
      
    - move: Hb1; simp is_grounded; bcase.
      have Htyeq : u.(ntype) = t.
        by apply/eqP; move: Hfapplies; rewrite /does_fragment_type_apply Hb1.
        rewrite exec_grounded_inlines_nil ?exec2_cat.
        have -> /= := (exec2_inlines_nil φ).
          by rewrite cats0; apply: IH => //; leq_queries_size; grounding.

          all: do ? by move: Hb2; rewrite are_grounded_inlines_E; case/andP.

          all: do ? by rewrite -Htyeq in Hb1 Hb0; apply: find_frags_nil_then_N_applies => //=; apply/eqP.                
  Qed.


  

End Theory.







(* Unused lemmas *)



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
  (*     forall u, u.(ntype) \in get_possible_types s ty -> *)
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
  (*       rewrite (find_not_similar_is_nil v.(ntype) (NestedField f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*           by rewrite IH //; ssromega. *)
            
  (*     + rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.  *)
  (*       congr cons; last by apply: IH => //; ssromega. *)
  (*       congr pair; congr Array. *)
  (*       apply/eq_in_map => v Hin. *)
  (*       rewrite (find_not_similar_is_nil v.(ntype) (NestedField f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*     + by rewrite IH //; ssromega. *)
        
  (*       * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs]. *)
  (*         simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].  *)
  (*         simp execute_selection_set; simp execute_selection_set2. *)
  (*         case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. *)
  (*         case: fld Hlook => f' args; case=> ty Hlook /=.  *)
  (*     + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. *)
  (*       rewrite (find_not_similar_is_nil v.(ntype) (NestedLabeledField l f α φ)) //; simp merge_selection_sets. *)
  (*         by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega. *)
  (*           by rewrite IH //; ssromega. *)
            
  (*     + rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.  *)
  (*       congr cons; last by apply: IH => //; ssromega. *)
  (*       congr pair; congr Array. *)
  (*       apply/eq_in_map => v Hin. *)
  (*       rewrite (find_not_similar_is_nil v.(ntype) (NestedLabeledField l f α φ)) //; simp merge_selection_sets. *)
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
  

