(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaLemmas.
Require Import SchemaWellFormedness.

Require Import Graph.
Require Import GraphConformance.
Require Import GraphLemmas.

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

Require Import QuerySemantics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Semantics Proofs</h1>
        <p class="lead">
         This file contains lemmas and proofs about the semantics of queries
         and selection sets.
        </p>         
        <p>
        In particular, we prove here that normalization preserves the semantics
        and that the simplified semantics is equivalent to the regular semantics, 
        whenever the queries are in normal form.
        </p>
  </div>
</div>#
 *)

Section Theory.
  Transparent qresponse_name has_response_name.

  Variables (Scalar : eqType)
            (s : wfGraphQLSchema)
            (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool)
            (g : conformedGraph s is_valid_scalar_value)
            (coerce : Scalar -> Scalar).
  
    
  (** We will be hiding several auxiliary definitions from the generated docs. They may still be seen 
      by looking at the source code. *)

  (* begin hide *)

   Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (property _ _) = _ |- context [ property _ _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ property ?u ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let svalue := fresh "svalue" in
        let lvalue := fresh "lvalue" in
        case Hv : (property u _) => [v |] /=; [case: v Hv => [svalue | lvalue] Hv |]

      | [|- context [(complete_value_clause_1 _ _ _ _ _ (?valid _ _ _))] ] =>
        let Hvalid := fresh "Hvalid" in
        case Hvalid : valid => //=

      | [|- context [complete_value _ _ _ (ftype ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let nty := fresh "nty" in
        let lty := fresh "lty" in
      
        case Hrty : fld.(ftype) => [nty | lty] /=

                      
      | [H : (ftype ?f) = _ |- context [ ftype ?f ] ] => rewrite H /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ _ _ (ftype ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(ftype) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [|- context[ execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ _ _ (ftype ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(ftype) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=

      | [|- context [execute_selection_set_unfold_clause_6 _ _ _ _ _ _ _ (does_fragment_type_apply _ _ _)] ] =>
        let Hfapplies := fresh "Hfapplies" in
        case Hfapplies : does_fragment_type_apply => //=
   
      | [|- context [complete_value] ] => simp complete_value
      | [ |- context [ execute_selection_set ] ] => simp execute_selection_set
      end.

  Ltac exec2 :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _] ] => rewrite H /=
      | [ H : (property _ _) = _ |- context [ property _ _] ] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _] ] => lookup
      | [|- context [ property _ ] ] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let svalue := fresh "svalue" in
        let lvalue := fresh "lvalue" in
        case Hv : (property _ _) => [v |] /=; [case: v Hv => [svalue | lvalue] Hv |]

                                                         
      | [H : (ftype ?f) = _ |- context [ ftype ?f ] ] => rewrite H /=
      | [H : (is_valid_scalar_value ?s ?nty ?c) = ?b |- context [is_valid_scalar_value ?s ?nty ?c] ] =>  rewrite H /=
      | [|- context [(complete_value_clause_1 _ _ _ _ _ (?valid _ _ _))] ] =>
        let Hvalid := fresh "Hvalid" in
        case Hvalid : valid => //=
  
      | [|- context [complete_value _ _ _ (ftype ?fld)] ] => case (ftype fld) => [nty | lty] /=                               

                           
      | [|- context[ simpl_execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ _ _ (ftype ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(ftype) => [rty | rty] /=

      | [|- context[ simpl_execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [|- context[ simpl_execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ _ _ (ftype ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(ftype) => [rty | rty] /=

      | [|- context[ simpl_execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [H : (ohead (neighbors_with_label _ _ _)) = _ |- context [ ohead (neighbors_with_label _ _ _)] ] =>
        rewrite H /=
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=

      | [|- context [complete_value] ] => simp complete_value
      | [ |- context [ simpl_execute_selection_set] ] => simp simpl_execute_selection_set
      end.

  (** ---- **)
  (**
     This lemma states that
   *)
  Lemma exec_frags_nil_func (f : Name -> seq (@Selection Scalar) -> seq Selection) u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    execute_selection_set s is_valid_scalar_value g coerce u  [seq InlineFragment t (f t φ) | t <- ptys] = [::].
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

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_frags_nil u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    execute_selection_set s is_valid_scalar_value g coerce u [seq InlineFragment t φ | t <- ptys] = [::].
  Proof.
      by apply: (exec_frags_nil_func (fun t qs => qs)).
  Qed.
 
  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_cat_frags_func (f : Name -> seq (@Selection Scalar) -> seq Selection) ptys u φ1 φ2 :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    execute_selection_set s is_valid_scalar_value g coerce u (φ1 ++ [seq InlineFragment t (f t φ2) | t <- ptys]) =
    execute_selection_set s is_valid_scalar_value g coerce u φ1.
  Proof.
    move=> Hfilterswap.
    move=> Hnin.
    move: {2}(selections_size _) (leqnn (selections_size φ1)) => n.
    elim: n φ1 φ2 => /= [| n IH] φ1 φ2; first by rewrite leqn0 => /selections_size_0_nil ->; apply: exec_frags_nil_func.
    case: φ1 => //= [Hleq|q φ1]; first by apply: exec_frags_nil_func.
    have Hinlineswap : forall ptys rname φ, [seq InlineFragment t (filter_queries_with_label rname (f t φ)) | t <- ptys] =
                                       [seq InlineFragment t (f t (filter_queries_with_label rname φ)) | t <- ptys].
      by elim=> //= t' ptys' IH' rname φ; rewrite Hfilterswap IH'.
      
      
      case_selection q; simp selection_size => Hleq Hobj Hunin; exec;
                                        rewrite ?filter_queries_with_label_cat ?filter_map_inline_func ?Hinlineswap ?IH //; leq_selections_size.

    - by congr cons; congr pair; congr Response.Object; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
        
    - by congr cons; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by congr cons; congr pair; congr Response.Object; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by congr cons; rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

    - by rewrite catA; apply: IH => //; leq_selections_size.
  Qed.

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_cat_frags ptys u φ1 φ2 :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys -> 
    execute_selection_set s is_valid_scalar_value g coerce u (φ1 ++ [seq InlineFragment t φ2 | t <- ptys]) =
    execute_selection_set s is_valid_scalar_value g coerce u φ1.
  Proof.
      by apply: (exec_cat_frags_func (fun t qs => qs)).
  Qed.

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_cat_frags_get_types ty u φ1 φ2 :
    u.(ntype) \notin get_possible_types s ty ->
    execute_selection_set s is_valid_scalar_value g coerce u (φ1 ++ [seq InlineFragment t φ2 | t <- get_possible_types s ty]) =
  execute_selection_set s is_valid_scalar_value g coerce u φ1.
  Proof.
      by move=> Hnin; apply: exec_cat_frags => //; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.
  

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_inlined_func (f : Name -> seq (@Selection Scalar) -> seq Selection) ptys u φ :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \in ptys ->
    execute_selection_set s is_valid_scalar_value g coerce u [seq InlineFragment t (f t φ) | t <- ptys] =
    execute_selection_set s is_valid_scalar_value g coerce u [:: InlineFragment u.(ntype) (f u.(ntype) φ) ]. 
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

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_inlined ptys u φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \in ptys ->
    execute_selection_set s is_valid_scalar_value g coerce u [seq InlineFragment t φ | t <- ptys] =     
    execute_selection_set s is_valid_scalar_value g coerce u [:: InlineFragment u.(ntype) φ ].
  Proof.
      by apply: (exec_inlined_func (fun t qs => qs)).
  Qed.

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma exec_filter_no_repeat rname φ u :
    all (fun kq => kq.1 != rname)
        (execute_selection_set s is_valid_scalar_value g coerce u (filter_queries_with_label rname φ)).
  Proof.
    move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname; first by rewrite leqn0 => /selections_size_0_nil ->.
    case: φ => //= q φ.
    case_selection q => //=; simp selection_size => Hleq; simp filter_queries_with_label.
    
    - case: eqP => //= /eqP Hneq; exec; apply_andP; rewrite filter_swap; apply: IH; leq_selections_size.
    - case: eqP => //= /eqP Hneq; exec; apply_andP; rewrite filter_swap; apply: IH; leq_selections_size.
      
    - case: eqP => //= /eqP Hneq; first by apply: IH; leq_selections_size.
      exec; do ? [apply_andP; rewrite filter_swap]; apply: IH; leq_selections_size.    
    - case: eqP => //= /eqP Hneq; first by apply: IH; leq_selections_size.
      exec; do ? [apply_andP; rewrite filter_swap]; apply: IH; leq_selections_size.
    - exec; rewrite -?filter_queries_with_label_cat; apply: IH; leq_selections_size.
  Qed.
      
  (* end hide *)


  (** * Non-redundancy of responses
      ----

      We prove that the semantics produces non-redundant responses.
   *)
  (**
     This lemma states that [complete_value] returns a non-redundant response.
   *)
  Lemma completed_value_are_non_redundant (ftype : type) (value : option (@Value Scalar)) : 
    Response.is_non_redundant (complete_value s is_valid_scalar_value coerce ftype value).
  Proof.
    funelim (complete_value s is_valid_scalar_value coerce ftype value) => //=.
    simp is_non_redundant.
    rewrite -map_comp /= all_map.
    apply/allP=> v Hin /=.
      by apply: H.
  Qed.

    (**
     This lemma states that the results of evaluating selections is non-redundant. 
     This means that there are no duplicated names in the response.
   *)
  Lemma exec_non_redundant φ u :
    Response.are_non_redundant (execute_selection_set s is_valid_scalar_value g coerce u φ).
  Proof.
    funelim (execute_selection_set s is_valid_scalar_value g coerce u φ) => //=.
    all: do ? [by apply_and3P; apply: exec_filter_no_repeat].
    - apply_and3P; [by apply: completed_value_are_non_redundant | by apply: exec_filter_no_repeat].
    - apply_and3P; [by apply: completed_value_are_non_redundant | by apply: exec_filter_no_repeat].     
      
    - apply_and3P; simp is_non_redundant.
      * rewrite all_map /=; apply/allP=> v Hin /=; by apply: H.
      * by apply: exec_filter_no_repeat.

  - apply_and3P; simp is_non_redundant.
      * rewrite all_map /=; apply/allP=> v Hin /=; by apply: H.
      * by apply: exec_filter_no_repeat.
  Qed.

  
  (** * Normalization preserves the semantics
      ----

      In this section we prove that, indeed, the normalization procedure 
      preserves the semantics of the original query.
   *)

  (**
     This lemma states that the semantics is preserved when normalizing with the the node's type
     where the selections are evaluated.
   *)
  Lemma normalize_selections_preserves_semantics φ u :
    u \in g.(nodes) ->
    execute_selection_set s is_valid_scalar_value g coerce u (normalize_selections s u.(ntype) φ) =
    execute_selection_set s is_valid_scalar_value g coerce u φ.
  Proof.    
    funelim (normalize_selections s u.(ntype) φ) => //=; do ? by exec.
    all: do ? [by intros; exec; rewrite filter_normalize_swap filter_filter_absorb // H]; exec => Huin.

    all: do ? [rewrite filter_normalize_swap filter_filter_absorb // H0 // -?filter_normalize_swap find_queries_filter_nil].
    - simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      congr cons; congr pair; congr Response.Object.
      have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbors_are_in_nodes.
      have Hvtype : v.(ntype) = rty.
        rewrite Hrty /= in Heq.
        apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(ntype) (Label name1 arguments1) = Some f by [].
        move/ohead_in: Hv => Hin.
        move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name1 arguments1) f Hlook v Hin).
          by rewrite Hrty.
      by apply: H => //; rewrite Hvtype.
      
    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      have Hvin : v \in g.(nodes).
        apply: neighbors_are_in_nodes; exact: Hin.
      have Hvtype : v.(ntype) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(ntype) (Label name1 arguments1) = Some f by [].
        move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name1 arguments1) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
      by apply: H => //; rewrite Hvtype.
            
    - simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Response.Object.
        rewrite exec_inlined_func //.
        simp execute_selection_set.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
          by apply/allP; apply: neighbors_are_in_nodes.
          have Hvobj := (node_in_graph_has_object_type Hvin).
          have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
          rewrite cats0.
            by apply: H.
            
              by apply: filter_normalize_swap.
                by apply: uniq_get_possible_types.
                  by apply/allP; apply: in_possible_types_is_object.

                  move/ohead_in: Hv => Hin.
                  move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name1 arguments1) f Heq0 v Hin).
                    by rewrite Hrty.
                    
      * congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Response.Object.
        simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
        simp execute_selection_set.
        have Hvin : v \in g.(nodes) by apply: neighbors_are_in_nodes; exact: Hin.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
            by apply: filter_normalize_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.  

                move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name1 arguments1) f Heq0 v Hin).
                  by rewrite Hrty.
                  

    - simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      congr cons; congr pair; congr Response.Object.
      have Hvin : v \in g.(nodes).
      apply: ohead_in_nodes; last by apply: Hv.
      apply/allP.
        by apply: neighbors_are_in_nodes.
      have Hvtype : v.(ntype) = rty.
      rewrite Hrty /= in Heq.
      apply: (in_object_possible_types Heq).
      have Hlook : lookup_field_in_type s u.(ntype) (Label name2 arguments2) = Some f by [].
      move/ohead_in: Hv => Hin.
      move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name2 arguments2) f Hlook v Hin).
        by rewrite Hrty.
          by apply: H => //; rewrite Hvtype.
              
              
    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0.
      rewrite Hrty /= in H.
      have Hvin : v \in g.(nodes).
      apply: neighbors_are_in_nodes; exact: Hin.
      have Hvtype : v.(ntype) = rty.
      rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
      have Hlook : lookup_field_in_type s u.(ntype) (Label name2 arguments2) = Some f by [].
      move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name2 arguments2) f Hlook v Hin).
        by rewrite Hrty /=. (* ?? *)
          by apply: H => //; rewrite Hvtype.
            
    - simp merge_selection_sets => /=; rewrite cats0.
      congr cons; congr pair; congr Response.Object.
      rewrite exec_inlined_func //.
      simp execute_selection_set.
      have Hvin : v \in g.(nodes).
      apply: ohead_in_nodes; last by apply: Hv.
        by apply/allP; apply: neighbors_are_in_nodes.
        have Hvobj := (node_in_graph_has_object_type Hvin).
        have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
        rewrite cats0.
          by apply: H.
          
            by apply: filter_normalize_swap.
              by apply: uniq_get_possible_types.
                by apply/allP; apply: in_possible_types_is_object.
                
                move/ohead_in: Hv => Hin.
                move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name2 arguments2) f Heq0 v Hin).
                  by rewrite Hrty.
                  

    - congr cons; congr pair; congr Array.
      apply/eq_in_map => v Hin; congr Response.Object.
      simp merge_selection_sets => /=; rewrite cats0 exec_inlined_func.
      simp execute_selection_set.
      have Hvin : v \in g.(nodes) by apply: neighbors_are_in_nodes; exact: Hin.
      have Hvobj := (node_in_graph_has_object_type Hvin).
      have -> /= : does_fragment_type_apply s v.(ntype) v.(ntype) by apply: object_applies_to_itself.
      rewrite cats0.
        by apply: H.
          by apply: filter_normalize_swap.
            by apply: uniq_get_possible_types.
              by apply/allP; apply: in_possible_types_is_object.  
              
              move: (@neighbors_are_subtype_of_field Scalar s is_valid_scalar_value g u (Label name2 arguments2) f Heq0 v Hin).
                by rewrite Hrty.
  Qed.


  (** ---- *)
  (**
     This theorem states that normalizing preserves the semantics of a query.
   *)
  Theorem normalize_preserves_query_semantics q :
    execute_query s is_valid_scalar_value g coerce (normalize s q) =
    execute_query s is_valid_scalar_value g coerce q.
  Proof.
    case: q => n ss; rewrite /execute_query /= -(root_query_type g).    
      by apply: normalize_selections_preserves_semantics; apply: root_in_nodes.
  Qed.



  
  (* begin hide *)
  
  Transparent is_field.

  (**
     This lemma states that [execute_selection_set2] distributes over list concatenation.
   *)
  Lemma exec2_cat u φ β :
    simpl_execute_selection_set s is_valid_scalar_value g coerce u (φ ++ β) =
    simpl_execute_selection_set s is_valid_scalar_value g coerce u φ ++
    simpl_execute_selection_set s is_valid_scalar_value g coerce u β. 
  Proof.
    move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
    elim: n φ β => /= [| n IH] φ β; first by rewrite leqn0 => /selections_size_0_nil ->.
    case: φ => // q φ; case_selection q; simp selection_size => Hleq; exec2; rewrite -/cat ?IH //; leq_selections_size.
    
      by case does_fragment_type_apply => /=; rewrite ?catA; apply: IH; leq_selections_size.
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
    execute_selection_set s is_valid_scalar_value g coerce u φ = [::].
  Proof.
    funelim (execute_selection_set s is_valid_scalar_value g coerce u φ) => //=; bcase.
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
    simpl_execute_selection_set s is_valid_scalar_value g coerce u φ = [::].
  Proof.
    funelim (simpl_execute_selection_set s is_valid_scalar_value g coerce u φ) => //=; bcase.
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
  Lemma exec_inv_inlines_nil φ β u :
    all (fun q => q.(is_inline_fragment)) β ->
    all (fun q => if q is on t { _ } then
                 ~~ does_fragment_type_apply s u.(ntype) t
               else
                 true) β ->
    execute_selection_set s is_valid_scalar_value g coerce u (φ ++ β) =
    execute_selection_set s is_valid_scalar_value g coerce u φ. 
  Proof.
    move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
    elim: n φ β u => /= [| n IH] φ β u; first by rewrite leqn0 => /selections_size_0_nil -> /=; apply: exec_inlines_nil.
    case: φ => //= [_ | q φ]; first by apply: exec_inlines_nil.
    case_selection q; simp selection_size => Hleq; intros; exec; rewrite ?filter_queries_with_label_cat ?find_queries_with_label_cat ?[find_queries_with_label _ _ _ β]find_fragment_not_applies_is_nil // ?cats0 //.
    all: do ? congr cons.
    all: do ? [apply: IH => //; leq_selections_size].
    all: do ? by apply: filter_preserves_inlines.
    all: do ? by apply: filter_preserves_fragment_not_applies.

    - by rewrite catA; apply: IH; leq_selections_size.
  Qed.   


  (**
     This lemma states that if there is no grounded fragment with type condition 
     [ty], then no fragment applies to [ty].

     The idea is that grounded fragments have Object types as type condition and 
     the only way for an Object type to apply to another is that they are the same.
     
     See also:
     - [exec_equivalence]
   *)
  Lemma find_frags_nil_then_N_applies (φ : seq (@Selection Scalar)) ty :
    find_fragment_with_type_condition ty φ = [::] ->
    all (fun sel => if sel is InlineFragment t _ then
                   is_object_type s t
                 else
                   false) φ ->
    all (fun sel => if sel is on t { _ } then
                 ~~ does_fragment_type_apply s ty t
               else
                 true) φ.
  Proof.
    elim: φ => // q φ IH; case_selection q => //=.
    simp find_fragment_with_type_condition; case: eqP => //= /eqP Hneq Hfind; simp is_inline_fragment => /= /andP [Hobj Hinlines].
    apply_andP; last by apply: IH.
    rewrite /does_fragment_type_apply.
    move/is_object_type_wfP: Hobj => [intfs [flds ->] ].
    by case lookup_type => //=; case.
  Qed.


  (* end hide *)


  (** * Semantics equivalence
      ----
      
      In this section we prove that both the original semantics and the simplified one are equivalent, 
      when considering queries in normal form. 
   *)

  (**
   This lemma states that, in the presence of selections in normal form, 
   both the original semantics and the simplified one produce the same response.
   *)
  Lemma exec_sel_eq_simpl_exec u φ :
    are_in_normal_form s φ ->
    execute_selection_set s is_valid_scalar_value g coerce u φ =
    simpl_execute_selection_set s is_valid_scalar_value g coerce u φ.    
  Proof.
    rewrite /are_in_normal_form; case/andP; rewrite /are_in_ground_typed_nf; case/andP.
    move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
    elim: n φ u => /= [| n IH] φ u; first by rewrite leqn0 => /selections_size_0_nil ->.
    case: φ => //= q φ; case_selection q; simp selection_size => Hleq /=; simp is_inline_fragment => /=; rewrite ?orbF => Hshape; bcase; non_red => /=; bcase; last first.

    - exec; exec2.
      move: Hb1; bcase.
      * have Htyeq : u.(ntype) = t.
        apply/eqP; move: Hfapplies; rewrite /does_fragment_type_apply.
        move: Hb1 => /is_object_type_wfP [intfs [flds ->] ].
          by case lookup_type => //=; case.
        rewrite exec_inv_inlines_nil // ?exec2_cat.
        have -> //= := (exec2_inlines_nil φ).
        rewrite cats0; apply: IH => //; leq_selections_size; [apply/orP; left|];
                                     by apply/allP=> sel Hin; have /allP-/(_ sel Hin) := Hb5; case/andP.

        all: do ? [ apply: find_frags_nil_then_N_applies;
                    [ by rewrite Htyeq; apply/eqP
                    | by apply/allP=> sel Hin;
                         have /allP-/(_ sel Hin) := Hb2;
                         have /allP-/(_ sel Hin) {Hin} := Hshape;
                         case: sel => //= t' subs Hinl; case/andP
                    ]
                  ].
          
      * by apply: IH => //; leq_selections_size; apply/orP; right. 
         
    all: do ? exec; exec2.
    all: do ? [move=> Hb1; bcase].
    all: do ? congr cons.
    all: do ? rewrite filter_find_fields_nil_is_nil //; do ? by apply/eqP.
    all: do ? apply: IH => //; leq_selections_size.
    all: do ? [by apply/orP; left].
    all: do ? congr pair.
    all: do ? [congr Array; apply/eq_in_map=> v Hin].
    all: do ? congr Response.Object.
    
    all: do ? [rewrite find_queries_nil_if_find_fields_nil// /merge_selection_sets /= ?cats0 in IH *; last by apply/eqP].
    all: do ? [by apply: IH => //; leq_selections_size; move: Hb1; bcase].

    simp simpl_execute_selection_set; rewrite Hlook /= Hv Hrty /=; simp complete_value.
      by rewrite IH //; rewrite Hshape.
    simp simpl_execute_selection_set; rewrite Hlook /= Hv Hrty /=; simp complete_value.
      by rewrite IH //; rewrite Hshape.
    
  Qed.

  (** ---- *)
  (**
     This theorem states that, in the presence of a query in normal form, 
     both the original semantics and the simplified semantics produce the same 
     response.
   *)
  Theorem exec_query_eq_simpl_exec q :
    is_in_normal_form s q -> 
    execute_query s is_valid_scalar_value g coerce q =
    simpl_execute_query s is_valid_scalar_value g coerce q.
  Proof.
    case: q => n ss.
    rewrite /is_in_normal_form /= /simpl_execute_query /execute_query /=.
      by apply: exec_sel_eq_simpl_exec => //=.
  Qed.

  (** ---- **)
  (**
   This corollary states that the evaluation of normalized selections 
   is equivalent in both semantics.
   *)
  Corollary exec_normalized_selections_eq_simpl_exec ss u :
    execute_selection_set s is_valid_scalar_value g coerce u (normalize_selections s u.(ntype) ss) =
    simpl_execute_selection_set s is_valid_scalar_value g coerce u (normalize_selections s u.(ntype) ss).
  Proof.
    apply: exec_sel_eq_simpl_exec => //=; rewrite /are_in_normal_form; apply_andP.
    - by apply: normalized_selections_are_grounded.
    - by apply: normalized_selections_are_non_redundant.
  Qed.

  (** ---- *)
  (**
     This corollary states that the evaluation of normalized selections 
     is equivalent in both semantics.
   *)
  Corollary exec_normalized_query_eq_simpl_exec q :
    execute_query s is_valid_scalar_value g coerce (normalize s q) =
    simpl_execute_query s is_valid_scalar_value g coerce (normalize s q).
  Proof.
      by apply: exec_query_eq_simpl_exec; apply: normalized_query_is_in_nf.
  Qed.
  
  
End Theory.

(**
   This finalizes the semantics and proofs of preservation and equivalence. 
        
   More can be found in the example files, implementing from schema, graphs, to queries 
   and responses.
 *)


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QuerySemantics.html' class="btn btn-light" role='button'>Previous ← Query Semantics</a>
    </div>#
*)