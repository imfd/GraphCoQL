From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fset fmap.


Require Import SeqExtra.

Require Import Schema.
Require Import SchemaAux.

Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.

Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.
Require Import QueryConformance.
Require Import QuerySemantic.
Require Import NRGTNF.

Require Import ValidFragments.

Require Import QueryRewrite.

Section Eq.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.



 

  
 



 
 
    
  
  Lemma nrl_subqueries (n : Name) (ϕ ϕ' : seq (seq (@ResponseObject Name Vals))) : ϕ = ϕ' -> NestedListResult n ϕ = NestedListResult n ϕ'. Proof. by move=> ->. Qed.


 
  Lemma qwe schema (g : @conformedGraph Name Vals schema) u qs qs' α n :
    (forall u : node_eqType Name Vals, u \in nodes g -> eval_queries schema g u qs = eval_queries schema g u qs') ->
    [seq (eval_queries schema g v qs) | v <- neighbours_with_field g u {| label := n; args := α |}] =
  [seq (eval_queries schema g v qs') | v <- neighbours_with_field g u {| label := n; args := α |}].
  Proof. Admitted.

 


 

  Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
    And6 of P1 & P2 & P3 & P4 & P5 & P6.
  Variables (T : Type) (P1 P2 P3 P4 P5 P6: T -> Prop).
  Variable b1 b2 b3 b4 b5 b6 : bool.

  Local Notation a P := (forall x, P x).

  Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.

  Lemma all_and6 : implies (forall x, [/\ P1 x, P2 x, P3 x, P4 x, P5 x & P6 x])
                           [/\ a P1, a P2, a P3, a P4, a P5 & a P6].
  Proof. by split=> haveP; split=> x; case: (haveP x). Qed.

  Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
  Proof.
      by case b1; case b2; case b3; case b4; case b5; case b6; constructor; try by case.
  Qed.

  
  Theorem all_q_has_nrgtnf_q schema (g : @conformedGraph Name Vals schema):
    forall (ϕ : @Query Name Vals),
      query_conforms schema schema.(query_type) ϕ ->
      Correct schema (schema.(query_type), schema.(query_type)) ϕ ->

      exists (ϕ' : seq (@Query Name Vals)),
        [/\
         queries_conform schema schema.(query_type) ϕ',
         are_in_normal_form schema ϕ',
         are_non_redundant ϕ',
         multi (QueryRewrite schema schema.(query_type)) [:: ϕ] ϕ' &
         eval schema g g.(root) ϕ = eval_queries schema g g.(root) ϕ'].
  Proof.
    move=> ϕ.
    elim ϕ using Query_ind with
        (Pl := fun qs =>
                forall root current,
                  queries_conform schema current qs ->
                  Forall (Correct schema (root, current)) qs ->
                  exists (qs' : seq Query),
                    [/\
                     queries_conform schema current qs',
                     are_in_normal_form schema qs',
                     are_non_redundant qs',
                     multi (QueryRewrite schema current) qs qs' &
                     forall u, u \in nodes g -> eval_queries schema g u qs = eval_queries schema g u qs']).

    - move=> f α; exists [:: (SingleField f α)]; split => //.
      by rewrite /queries_conform /all; apply/andP; split => //; apply/andP.
      by apply: multi_refl.
    - move=> l f α; exists [:: (LabeledField l f α)]; split => //.
      by rewrite /queries_conform /all; apply/andP; split=> //; apply/andP.
      by apply: multi_refl.              

    - move=> f α qs IH Hqc Hok.
      (* Get the field defined in the schema *)
      move: (nf_conforms_lookup_some Hqc); case=> fld Hlook.
      (* Get the proof that the subquery conforms according to the field's type *)
      move: (nf_queries_conform'' Hlook Hqc) => Hqsc.
      (* Get the field's type - Why not simpler to get? *)
      move: (nf_correct_lookup_some Hok); case=> ty' Hlook'.
      (* Get proof that subqueries are free of issues *)
      move: (nested_field_subqueries_correct Hok Hlook').
      move: Hqsc.
      move: (lookup_field_or_type Hlook Hlook') => Heq; rewrite -Heq => Hqsc Hqsok.
      move: (IH ty' ty' Hqsc Hqsok) => {IH}; case=> qs' [Hqsc' Hqsnf' Hqsnr' Hred' Hev'].
      
      exists [:: (NestedField f α qs')]; split => //=.
      * rewrite /queries_conform /all; apply/andP; split=> //.
        rewrite /query_conforms Hlook -/(query_conforms _ _).
        apply/andP; split=> //.
        apply/and3P; split=> //.
        apply/norP.
        move
      * rewrite /are_in_normal_form.
        apply/andP; split=> //.
        rewrite /all /is_in_normal_form. by apply/andP.
      * rewrite /are_non_redundant.
        apply/andP; split=> //.
        rewrite /all /is_non_redundant. by apply/andP.
      (* Proof of rewriting *)
      * apply: multi_step.
        apply: SQ => //.
        apply: multi_step.
          by apply: (AQR_Nested Hqc Hlook' Hred').
        by apply: multi_refl.
        by apply: multi_refl.
      (* Proof of evaluating to the same *)    
      * move: (root_in_nodes g) => Hrootin.
        case: lookup_field_type => //.
        (* Check the type of the node; named type or list type *)
        case=> [nt | lt].
        + case E: get_target_nodes_with_field => [|v tl] //.
            case OH: ohead => [v'|] //.
            inversion OH.
            rewrite -E in OH.
            move: (@u_and_target_nodes_in_nodes g g.(root) (Field f α) Hrootin) => Hall.
            move: (ohead_in_nodes Hall OH) => Hv'.
            move: (Hev' v' Hv').
            by rewrite -/(eval_queries _ _ _) => ->.
        + apply: singleton; apply: nrl_subqueries.
            by apply: qwe; apply: Hev'.

    (* LabeledField is similar to previous case *)
    - move=> l f α qs IH Hqc Hok.
      move: (nlf_conforms_lookup_some Hqc); case=> fld Hlook.
      move: (nlf_queries_conform'' Hlook Hqc) => Hqsc.
      move: (nlf_correct_lookup_some Hok); case=> ty' Hlook'.
      move: (nlf_queries_correct Hlook' Hok).
      move: Hqsc.
      move: (lookup_field_or_type Hlook Hlook') => Heq; rewrite -Heq => Hqsc Hqsok.
      move: (IH ty' ty' Hqsc Hqsok); case=> qs' [Hqne' Hqsok' Hqsnf' Hqsnr' Hred' Hev'].
      
      exists [:: (NestedLabeledField l f α qs')]; split => //=.
       * apply: Forall_cons => //=.
        apply: CNLF => //.
        move: Hqc.
        rewrite /query_conforms Hlook.
        case: ifP => // _.
        move/and3P=> [_ Hargs _].
        rewrite /queries_conform -Heq.
        apply/and3P; split=> //.
        apply: (queries_correct_conform Hqsok').
        apply: Hlook'.
        apply: Hqsok'.
      * rewrite /are_in_normal_form.
        apply/andP; split=> //.
        rewrite /all /is_in_normal_form. by apply/andP.
      * rewrite /are_non_redundant.
        apply/andP; split=> //.
        rewrite /all /is_non_redundant. by apply/andP.
         (* Proof of rewriting *)
      * apply: multi_step.
        apply: SQ => //.
        apply: multi_step.
          by apply: (AQR_LabeledNested Hqc Hlook' Hred').
        by apply: multi_refl.
          by apply: multi_refl.
      * move: (root_in_nodes g) => Hrootin.
        case: lookup_field_type => //.
        (* Check the type of the node; named type or list type *)
        case=> [nt | lt].
        + case E: get_target_nodes_with_field => [|v tl] //.
            case OH: ohead => [v'|] //.
            inversion OH.
            rewrite -E in OH.
            move: (@u_and_target_nodes_in_nodes g g.(root) (Field f α) Hrootin) => Hall.
            move: (ohead_in_nodes Hall OH) => Hv'.
            move: (Hev' v' Hv').
            by rewrite -/(eval_queries _ _ _) => ->.
        + apply: singleton; apply: nrl_subqueries.
            by apply: qwe; apply: Hev'.

      
    (* InlineFragment *)        
    - move=> t qs IH Hqc Hok.
      (* Get proof that subqueries conform *)
      move: (inline_subqueries_conform Hqc) => Hqsc.
      (* Get proof that subqueries are free of issues *)
      move: (inline_subqueries_correct Hok) => Hqsok.
      move: (IH schema.(query_type) t Hqsc Hqsok) => {IH}; case=> qs' [Hqsne' Hqsok' Hqsnf' Hqsnr' Hred' Hev'].
      move: (query_type_object_wf_schema schema) => Hqobj.
      move: (are_in_normal_form_E Hqsnf') => [Hqs' Hallqsnf'].
      pose Hqc' := Hqc.
      move: Hqc'.
      rewrite /query_conforms.      
      move/and4P=> [/or3P [Hobj | Hint | Hunion] Hspread _ _]; exists qs'.
      * move: (object_spreads_in_object_scope Hqobj Hobj Hqsc).
        case.
        move/(_ Hqc) => Heq _; rewrite -Heq.
        split=> //.
          by rewrite Heq; rewrite Heq in Hqsok'.
        apply: multi_step => //.
        rewrite -Heq in Hqc.
        apply: Inline_same => //.
        apply: Hred'.
        move: (Hev' g.(root) (root_in_nodes g)) => <-.
        rewrite Heq.
          by apply (eval_query_inline g qs).
      * move: (interface_spreads_in_object_scope Hqobj Hint Hqc) => Himpl.
        split=> //.
        + apply: (queries_correct_impl Himpl Hqsok').
        + apply: multi_step.
          apply: SQ => //.
          apply: multi_step => //.
          apply (AQR_Inline Hqc Hred')  => //.
          apply: multi_refl.

          apply: multi_step => //.
          apply: SQ => //.
          apply: (foo Hqobj Hint Hspread Hqsne' Hqsok').
          apply: multi_step.
          apply: AQR_Inline_Impl => //.
          apply: (foo Hqobj Hint Hspread Hqsne' Hqsok').
          apply: multi_refl.
          apply: multi_step.
          apply: Inline_same.
          apply: inline_conforms_to_same_type => //.
            by constructor 1.
          move: (foo Hqobj Hint Hspread Hqsne' Hqsok').
          rewrite /query_conforms.
          move/and4P=> [_ _ _].
          move/(queries_conform_inv Hqsne')=> Hqsc'.
          apply: (bleble Himpl Hqsc' Hqsok').
          apply: multi_refl.
        + rewrite eval_equation_5.
          move/is_interface_type_E: Hint => [i [flds ->]].
          move: (root_query_type g) => ->.
          move/declares_in_implementation: Himpl => ->.
          apply: (Hev' g.(root) (root_in_nodes g)).
     * move: (union_spreads_in_object_scope Hqobj Hunion Hqc) => Hmb.
       split=> //.
       + apply: (queries_correct_mb Hmb Hqsok').
       + apply: multi_step.
          apply: SQ => //.
          apply: multi_step => //.
          apply (AQR_Inline Hqc Hred')  => //.
          apply: multi_refl.

          apply: multi_step => //.
          apply: SQ => //.
          apply: (foo' Hqobj Hunion Hspread Hqsne' Hqsok').
          apply: multi_step.
          apply: AQR_Inline_Member => //.
          apply: (foo' Hqobj Hunion Hspread Hqsne' Hqsok').
          apply: multi_refl.
          apply: multi_step.
          apply: Inline_same.
          apply: inline_conforms_to_same_type => //.
            by constructor 1.
          move: (foo' Hqobj Hunion Hspread Hqsne' Hqsok').
          rewrite /query_conforms.
          move/and4P=> [_ _ _].
          move/(queries_conform_inv Hqsne')=> Hqsc'.
          apply: (bleble' Hmb Hqsc' Hqsok').
          apply: multi_refl.
       + rewrite eval_equation_5.
         move/is_union_type_E: Hunion => [u [mbs Hlook]].
         move: (root_query_type g) => ->.
         rewrite /union_members in Hmb.
         rewrite Hlook in Hmb.
         rewrite Hlook Hmb.
         apply: (Hev' g.(root) (root_in_nodes g)).
    (* Empty list *)
     * done.
    
     * 
       
End Eq.