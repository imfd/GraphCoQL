(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Graph.
Require Import GraphConformance.
Require Import GraphConformanceLemmas.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.
Require Import QueryConformanceLemmas.

Require Import Response.

Require Import QueryNormalForm.
Require Import QueryNormalFormLemmas.


Require Import SeqExtra.
Require Import QueryTactics.
Require Import GeneralTactics.

Require Import QuerySemantic.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Semantics</h1>
        <p class="lead">
         This file contains lemmas and theory about the semantics of queries.
        </p>         
        <p>
        In particular, we prove here that normalisation preserves the semantics
        and that the simplified semantics is equivalent to the regular semantics, 
        whenever the queries are in normal form.
        </p>
        <p>
        Having this, we can satisfy the statement by Pérez & Hartig, that for every query 
        there is a normalised version with the same semantics, and that we can replace 
        one semantics for the other.
        </p>
  </div>
</div>#
 *)

Section Theory.
  Transparent qresponse_name has_response_name.

  (** We will be hiding several auxiliary definitions from the generated docs. They may still be seen 
      by looking at the source code. *)

  (* begin hide *)
  Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (field_seq_value (nprops _) _) = _ |- context [ field_seq_value (nprops _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ field_seq_value ?u.(nprops) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (field_seq_value u.(nprops) _) => [ [v | vs] |] /=

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
      | [ H : (field_seq_value (nprops _) _) = _ |- context [ field_seq_value (nprops _) _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ field_seq_value ?u.(nprops) ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (field_seq_value u.(nprops) _) => [ [v | vs] |] /=

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
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj].
    rewrite /negb; case: ifP => //=.
    rewrite inE => /negbT-/norP [/negbTE Hneq Hunin] _.
    simp execute_selection_set; rewrite /does_fragment_type_apply.
    case Hlook: lookup_type => //= [tdef|]; last by apply: IH.
    case: tdef Hlook => //=; do ? by intros; apply: IH.
    intros.
    move: Hobj; simp is_object_type; case Hlook2: lookup_type => [tdef|] //=; case: tdef Hlook2 => //=; intros.
    move: Hneq.
    rewrite (lookup_type_name_wf Hlook) (lookup_type_name_wf Hlook2) => -> /=.
      by apply: IH.
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
    elim: ptys => //= t ptys IH /andP [Hnin Huniq] /andP [/is_object_type_wfP [intfs [flds Hlook] ] Hinobj].
    rewrite inE => /orP [/eqP Heq | Hin].
    - rewrite -Heq in Hnin *; simp execute_selection_set.
      have -> /= : does_fragment_type_apply s u.(ntype) u.(ntype).
      by apply: object_applies_to_itself; rewrite Heq; simp is_object_type; rewrite Hlook.
          by rewrite cats0; apply: exec_cat_frags_func.
          
    - rewrite {1}execute_selection_set_equation_6.
      have -> /= : does_fragment_type_apply s u.(ntype) t = false.
      rewrite /does_fragment_type_apply.
      move/memPn: Hnin => /(_ u.(ntype) Hin) /negbTE Hneq.
      case lookup_type => //=; case=> //=; intros.
        by rewrite Hlook.

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

  (* end hide *)
  

  (** * Normalisation proofs *)
  (** ---- *)
  (**
     This lemma states that the semantics is preserved when normalizing with the the node's type
     where the queries are evaluated.
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


  (** ---- *)
  (**
     This theorem states that the semantics is preserved when normalizing with a supertype
     of the node's type where the queries are evaluated.
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



  (** ---- *)
  (**
     This theorem states that the semantics are preserved when normalizing 
     with the Query type, evaluating from the root node and if the queries
     conform to the Query type. 
   *)
  (* Conformance doesn't affect this at all... This is a particular case of 
     the previous theorem *)
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



  (* begin hide *)
  
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
    apply_andP; last by apply: IH.
    rewrite /does_fragment_type_apply.
    move/is_object_type_wfP: Hb0 => [intfs [flds ->] ].
    by case lookup_type => //=; case.
  Qed.


  (* end hide *)


  (** * Semantics equivalence *)
  (** ---- *)
  (**
     This theorem states that in the presence of a query in normal form, 
     both the semantics with collection and the simplified semantics are 
     equivalent.
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
      apply/eqP; move: Hfapplies; rewrite /does_fragment_type_apply.
      move/is_object_type_wfP: Hb1 => [intfs [flds ->] ].
        by case lookup_type => //=; case.

      rewrite exec_grounded_inlines_nil ?exec2_cat.
      have -> /= := (exec2_inlines_nil φ).
        by rewrite cats0; apply: IH => //; leq_queries_size; grounding.

          all: do ? by move: Hb2; rewrite are_grounded_inlines_E; case/andP.

          all: do ? by rewrite -Htyeq in Hb1 Hb0; apply: find_frags_nil_then_N_applies => //=; apply/eqP.                
  Qed.

  
(** ---- *)
End Theory.
