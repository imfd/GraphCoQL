(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.


From Equations Require Import Equations.

Require Import String.
Require Import QString.

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

Require Import QuerySemantic.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Semantics Theory</h1>
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
        case Hv : (field_seq_value u.(nprops) _) => [ v |] /=

      | [H : is_true (is_valid_response_value _ _ _) |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=

      | [H : is_valid_response_value _ _ _ = _ |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=

      | [|- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        let Hvalid := fresh "Hvalid" in
        case: ifP => Hvalid //=
                      
      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [|- context[ execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
                               
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=

      | [|- context [execute_selection_set_unfold_clause_6 _ _ _ _ _ _ (does_fragment_type_apply _ _ _)] ] =>
        let Hfapplies := fresh "Hfapplies" in
        case Hfapplies : does_fragment_type_apply => //=
   
      | [ |- context [ _, _ ⊢ ⟦ _ ⟧ˢ in _ with _] ] => simp execute_selection_set
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
        case Hv : (field_seq_value u.(nprops) _) => [ v |] /=

      | [H : is_true (is_valid_response_value _ _ _) |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=
                
      | [H : is_valid_response_value _ _ _ = _ |- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        rewrite H /=

    
      | [|- context [if is_valid_response_value _ _ _ then _ else _] ] =>
        let Hvalid := fresh "Hvalid" in
        case: ifP => Hvalid //=
                           
      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [H : (return_type ?f) = _ |- context [ return_type ?f ] ] => rewrite H /=

      | [|- context[ simpl_execute_selection_set_unfold_clause_4_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ simpl_execute_selection_set_unfold_clause_4_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [|- context[ simpl_execute_selection_set_unfold_clause_5_clause_1 _ _ _ _ _ (return_type ?fld)] ] =>
        let Hrty := fresh "Hrty" in
        let rty := fresh "rty" in
        case Hrty : fld.(return_type) => [rty | rty] /=

      | [|- context[ simpl_execute_selection_set_unfold_clause_5_clause_1_clause_2 _ _ _ _ _ _ _ (ohead _)] ] =>
        let Hv := fresh "Hv" in
        case Hv : ohead => [v|] //=
     
      | [H : (ohead (neighbors_with_field _ _ _)) = _ |- context [ ohead (neighbors_with_field _ _ _)] ] =>
        rewrite H /=
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _] ] => rewrite H /=
      | [ |- context [ _, _ ⊢ ≪ _ ≫ in _ with _] ] => simp simpl_execute_selection_set
      end.


  Variables (Val : eqType) (s : @wfGraphQLSchema Val) (g : conformedGraph s) (coerce : @wfCoercion Val).


  
  Lemma exec_frags_nil_func (f : Name -> seq (@Selection Val) -> seq Selection) u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u with coerce = [::].
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
    s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u with coerce = [::].
  Proof.
      by apply: (exec_frags_nil_func (fun t qs => qs)).
  Qed.
 

  Lemma exec_cat_frags_func (f : Name -> seq (@Selection Val) -> seq Selection) ptys u φ1 φ2 :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \notin ptys ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t (f t φ2) | t <- ptys] ⟧ˢ in u with coerce = s, g ⊢ ⟦ φ1 ⟧ˢ in u with coerce.
  Proof.
    move=> Hfilterswap.
    move=> Hnin.
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n φ1 φ2 => /= [| n IH] φ1 φ2; first by rewrite leqn0 => /queries_size_0_nil ->; apply: exec_frags_nil_func.
    case: φ1 => //= [Hleq|q φ1]; first by apply: exec_frags_nil_func.
    have Hinlineswap : forall ptys rname φ, [seq InlineFragment t (filter_queries_with_label rname (f t φ)) | t <- ptys] =
                                       [seq InlineFragment t (f t (filter_queries_with_label rname φ)) | t <- ptys].
      by elim=> //= t' ptys' IH' rname φ; rewrite Hfilterswap IH'.
      
      
      case_selection q; simp selection_size => Hleq Hobj Hunin; exec;
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
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- ptys] ⟧ˢ in u with coerce = s, g ⊢ ⟦ φ1 ⟧ˢ in u with coerce.
  Proof.
      by apply: (exec_cat_frags_func (fun t qs => qs)).
  Qed.

  Lemma exec_cat_frags_get_types ty u φ1 φ2 :
    u.(ntype) \notin get_possible_types s ty ->
    s, g ⊢ ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- get_possible_types s ty] ⟧ˢ in u with coerce =
                                                                          s, g ⊢ ⟦ φ1 ⟧ˢ in u with coerce.
  Proof.
      by move=> Hnin; apply: exec_cat_frags => //; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.
  

  
  Lemma exec_inlined_func (f : Name -> seq (@Selection Val) -> seq Selection) ptys u φ :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(ntype) \in ptys ->
                 s, g ⊢ ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u with coerce =  s, g ⊢ ⟦ [:: InlineFragment u.(ntype) (f u.(ntype) φ) ] ⟧ˢ in u with coerce. 
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
                 s, g ⊢ ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u with coerce =  s, g ⊢ ⟦ [:: InlineFragment u.(ntype) φ ] ⟧ˢ in u with coerce. 
  Proof.
      by apply: (exec_inlined_func (fun t qs => qs)).
  Qed.


  Lemma exec_filter_no_repeat rname φ u :
    all (fun kq => kq.1 != rname)
        (s, g ⊢ ⟦ filter_queries_with_label rname φ ⟧ˢ in u with coerce).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ.
    case_selection q => //=; simp selection_size => Hleq; simp filter_queries_with_label.
    
    - case: eqP => //= /eqP Hneq; exec; apply_andP; rewrite filter_swap; apply: IH; leq_queries_size.
    - case: eqP => //= /eqP Hneq; exec; apply_andP; rewrite filter_swap; apply: IH; leq_queries_size.
      
    - case: eqP => //= /eqP Hneq; first by apply: IH; leq_queries_size.
      exec; do ? [apply_andP; rewrite filter_swap]; apply: IH; leq_queries_size.    
    - case: eqP => //= /eqP Hneq; first by apply: IH; leq_queries_size.
      exec; do ? [apply_andP; rewrite filter_swap]; apply: IH; leq_queries_size.
    - exec; rewrite -?filter_queries_with_label_cat; apply: IH; leq_queries_size.
  Qed.
      
  (* end hide *)


  (** * Non-redundancy of responses *)
  (** ---- *)
  (**
     This lemma states that the results of evaluating queries is non-redundant. 
     This means that there are no duplicated names in the response.

     The proof actually requires that the coercion function gives a non-redundant
     value.
   *)
  Lemma exec_non_redundant φ u :
    Response.are_non_redundant (s, g ⊢  ⟦ φ ⟧ˢ in u with coerce).
  Proof.
    funelim (s, g ⊢  ⟦ φ ⟧ˢ in u with coerce) => //=.
    all: do ? [by apply_and3P; apply: exec_filter_no_repeat].
    - case: ifP => //= _; apply_and3P; do ? first [ by apply: exec_filter_no_repeat | by apply: H].
        by case: coerce.
        
    - case: ifP => //= _; apply_and3P; do ? first [ by apply: exec_filter_no_repeat | by apply: H].
        by case: coerce. 
      
    - apply_and3P.
      * simp is_non_redundant.
        elim: neighbors_with_field => //= v neighbors IH; apply_andP.
        simp is_non_redundant.
          by apply: H.
      * by apply: exec_filter_no_repeat.

    - apply_and3P.
      * simp is_non_redundant.
        elim: neighbors_with_field => //= v neighbors IH; apply_andP.
        simp is_non_redundant.
          by apply: H.
      * by apply: exec_filter_no_repeat.
  Admitted. (* Error again :/ ... No subgoals *)
  
      
  (** * Normalisation proofs *)
  (** ---- *)
  (**
     This lemma states that the semantics is preserved when normalizing with the the node's type
     where the queries are evaluated.
   *)
  Lemma normalize_selections_preserves_semantics φ u :
    u \in g.(nodes) ->
    s, g ⊢ ⟦ normalize_selections s u.(ntype) φ ⟧ˢ
        in u with coerce =
    s, g ⊢ ⟦ φ ⟧ˢ in u with coerce. 
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
        move: (@neighbors_are_subtype_of_field Val s g u (Label name1 arguments1) f Hlook v Hin).
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
        move: (@neighbors_are_subtype_of_field Val s g u (Label name1 arguments1) f Hlook v Hin).
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
                  move: (@neighbors_are_subtype_of_field Val s g u (Label name1 arguments1) f Heq0 v Hin).
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

                move: (@neighbors_are_subtype_of_field Val s g u (Label name1 arguments1) f Heq0 v Hin).
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
      move: (@neighbors_are_subtype_of_field Val s g u (Label name2 arguments2) f Hlook v Hin).
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
      move: (@neighbors_are_subtype_of_field Val s g u (Label name2 arguments2) f Hlook v Hin).
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
                move: (@neighbors_are_subtype_of_field Val s g u (Label name2 arguments2) f Heq0 v Hin).
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
              
              move: (@neighbors_are_subtype_of_field Val s g u (Label name2 arguments2) f Heq0 v Hin).
                by rewrite Hrty.
  Qed.


  (** ---- *)
  (**
     This theorem states that normalizing preserves the semantics of a query.
   *)
  Theorem normalize_preserves_query_semantics q :
    execute_query s g coerce (normalize s q) =
    execute_query s g coerce q.
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
    s, g ⊢ ≪ φ ++ β ≫ in u with coerce = s, g ⊢ ≪ φ ≫ in u with coerce ++ s, g ⊢ ≪ β ≫ in u with coerce. 
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ β => /= [| n IH] φ β; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => // q φ; case_selection q; simp selection_size => Hleq; exec2; rewrite -/cat ?IH //; leq_queries_size.    
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
    s, g ⊢ ⟦ φ ⟧ˢ in u with coerce = [::].
  Proof.
    funelim (execute_selection_set s g _ u _) => //=; bcase.
      by rewrite Heq in Hb0.
        by apply: H => //; intros; apply: (Hnappl q) => //; apply: mem_tail.
  Admitted. (* error ? - Maybe related to https://github.com/coq/coq/issues/4085 *)

 
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
    s, g ⊢ ≪ φ ≫ in u with coerce = [::].
  Proof.
    funelim (s, g ⊢ ≪ φ ≫ in u with coerce) => //=; bcase.
      by rewrite Heq in Hb0.
        by apply: H => //; intros; apply: (Hnappl q) => //; apply: mem_tail.
  Admitted. (* Error - maybe related to https://github.com/coq/coq/issues/4085 *)
  
 

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
    s, g ⊢ ⟦ φ ++ β ⟧ˢ in u with coerce = s, g ⊢  ⟦ φ ⟧ˢ in u with coerce. 
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ β u => /= [| n IH] φ β u; first by rewrite leqn0 => /queries_size_0_nil -> /=; apply: exec_inlines_nil.
    case: φ => //= [_ | q φ]; first by apply: exec_inlines_nil.
    case_selection q; simp selection_size => Hleq; intros; exec; rewrite ?filter_queries_with_label_cat ?find_queries_with_label_cat ?[find_queries_with_label _ _ _ β]find_fragment_not_applies_is_nil // ?cats0 //.
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
  Lemma find_frags_nil_then_N_applies (φ : seq (@Selection Val)) ty :
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


  (** * Semantics equivalence *)
  (** ---- *)
  (**
     This theorem states that in the presence of a query in normal form, 
     both the semantics with collection and the simplified semantics are 
     equivalent.
   *)
  Lemma exec_sel_eq_simpl_exec u φ :
    are_in_normal_form s φ -> 
    s, g ⊢ ⟦ φ ⟧ˢ in u with coerce =
    s, g ⊢ ≪ φ ≫ in u with coerce. 
  Proof.
    rewrite /are_in_normal_form; case/andP; rewrite /are_in_ground_typed_nf; case/andP.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => /= [| n IH] φ u; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ; case_selection q; simp selection_size => Hleq /=; simp is_inline_fragment => /=; rewrite ?orbF => Hshape; bcase; non_red => /=; bcase; last first.

    - exec; exec2.
      move: Hb1; bcase.
      * have Htyeq : u.(ntype) = t.
        apply/eqP; move: Hfapplies; rewrite /does_fragment_type_apply.
        move: Hb1 => /is_object_type_wfP [intfs [flds ->] ].
          by case lookup_type => //=; case.
        rewrite exec_inv_inlines_nil // ?exec2_cat.
        have -> //= := (exec2_inlines_nil φ).
        rewrite cats0; apply: IH => //; leq_queries_size; [apply/orP; left|];
                                     by apply/allP=> sel Hin; have /allP-/(_ sel Hin) := Hb5; case/andP.

        all: do ? [ apply: find_frags_nil_then_N_applies;
                    [ by rewrite Htyeq; apply/eqP
                    | by apply/allP=> sel Hin;
                         have /allP-/(_ sel Hin) := Hb2;
                         have /allP-/(_ sel Hin) {Hin} := Hshape;
                         case: sel => //= t' subs Hinl; case/andP
                    ]
                  ].
          
      * by apply: IH => //; leq_queries_size; apply/orP; right. 
         
    all: do ? exec; exec2.
    all: do ? [move=> Hb1; bcase].
    all: do ? congr cons.
    all: do ? rewrite filter_find_fields_nil_is_nil //; do ? by apply/eqP.
    all: do ? apply: IH => //; leq_queries_size.
    all: do ? [by apply/orP; left].
    all: do ? congr pair.
    all: do ? [congr Array; apply/eq_in_map=> v Hin].
    all: do ? congr Response.Object.
    
    all: do ? [rewrite find_queries_nil_if_find_fields_nil// /merge_selection_sets /= ?cats0 in IH *; last by apply/eqP].
    all: do ? [by apply: IH => //; leq_queries_size; move: Hb1; bcase].              
  Qed.

  Theorem exec_query_eq_simpl_exec q :
    is_in_normal_form s q -> 
    execute_query s g coerce q =
    simpl_execute_query s g coerce q.
  Proof.
    case: q => n ss.
    rewrite /is_in_normal_form /= /simpl_execute_query /execute_query /=.
      by apply: exec_sel_eq_simpl_exec => //=.
  Qed.


  Corollary exec_normalized_selections_eq_simpl_exec ss u :
    s, g ⊢ ⟦ normalize_selections s u.(ntype) ss ⟧ˢ in u with coerce =
    s, g ⊢ ≪ normalize_selections s u.(ntype) ss ≫ in u with coerce.
  Proof.
    apply: exec_sel_eq_simpl_exec => //=; rewrite /are_in_normal_form; apply_andP.
    - by apply: normalized_selections_are_grounded.
    - by apply: normalized_selections_are_non_redundant.
  Qed.

  Corollary exec_normalized_query_eq_simpl_exec q :
    execute_query s g coerce (normalize s q) =
    simpl_execute_query s g coerce (normalize s q).
  Proof.
      by apply: exec_query_eq_simpl_exec; apply: normalized_query_is_in_nf.
  Qed.
  
  
(** ---- *)
End Theory.
