Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap fset.
From Equations Require Import Equations.


Require Import SchemaWellFormedness.
Require Import GraphConformance.
Require Import QueryConformance.
Require Import SchemaAux.
Require Import GraphAux.
Require Import QueryAux.

Require Import Schema.
Require Import Query.
Require Import Response.

Require Import Graph.

Require Import Ssromega.

Require Import SeqExtra.


Require Import NRGTNF.
Require Import QueryRewrite.

Require Import QueryTactics.


Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  
  Variable s : @wfSchema Name Vals.
  Variable g : @conformedGraph Name Vals s.
  
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type queries : seq (@Query Name Vals).

  Transparent qresponse_name has_response_name qname.

  Ltac field_defined :=
    repeat match goal with
           | [ H : is_true (are_defined _ (SingleField ?f _ :: ?qs) ?ty) |- context [lookup_field_in_type _ ?ty ?f ] ] =>
             
             let Hdefined := fresh "Hdefined"  in
             let Hlook := fresh "Hlook" in
             let fld := fresh "fld" in
             move: H; simp are_defined => /= /andP [/is_definedE [fld /= Hlook] Hdefined]; rewrite ?Hlook /=
                                                                                                  
           | [ H : is_true (are_defined _ (SingleField ?f _ :: ?qs) ?ty),
                   H2 : lookup_field_in_type _ ?ty ?f = Some _ |- _ ] =>
             let Hdefined := fresh "Hdefined"  in
             move: H; simp are_defined => /= /andP [_ Hdefined]    
                                            
           | [ H : is_true (are_defined _ (NestedField ?f _ _ :: ?qs) ?ty) |- context [lookup_field_in_type _ ?ty ?f ] ] =>
             let Hdefined := fresh "Hdefined"  in
             let Hlook := fresh "Hlook" in
             let fld := fresh "fld" in
             move: H; simp are_defined => /= /andP [/is_definedE [fld /= Hlook] Hdefined]; rewrite ?Hlook /=

                                                                                                  
           | [ H : is_true (are_defined _ (NestedField ?f _ _ :: ?qs) ?ty),
                   H2 : lookup_field_in_type _ ?ty ?f = Some _ |- _ ] =>
             let Hdefined := fresh "Hdefined"  in
             move: H; simp are_defined => /= /andP [_ Hdefined]    
                                            
                                            
           end.

  Lemma object_applies_to_itself ty :
    is_object_type s ty ->
    does_fragment_type_apply s ty ty.
  Proof.
      by rewrite /does_fragment_type_apply => ->.
  Qed.
  
  Reserved Notation "⟦ φ ⟧ˢ 'in' u" (at level 40).
  
  Equations? execute_selection_set u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      ⟦ [::] ⟧ˢ in _ := [::];
      
      ⟦ InlineFragment t φ :: qs ⟧ˢ in u
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⟦ φ ++ qs ⟧ˢ in u;
        | _ := ⟦ qs ⟧ˢ in u
        };

      ⟦ SingleField f α :: qs ⟧ˢ in u
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (SingleValue value)) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u;
            | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u;
            | None => (f, Leaf Null) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u  (* Should throw error? *)
            };
        | _ := ⟦ qs ⟧ˢ in u (* Should throw error *)
        };
      
      ⟦ LabeledField l f α :: qs ⟧ˢ in u
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (SingleValue value)) :: ⟦ filter_queries_with_label l qs ⟧ˢ in u;
            | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⟦ filter_queries_with_label l qs ⟧ˢ in u;
            | None => (l, Leaf Null) :: ⟦ filter_queries_with_label l qs ⟧ˢ in u (* Should throw error? *)
            };

        | _ := ⟦ qs ⟧ˢ in u (* Should throw error *)
        };

      
      ⟦ NestedField f α φ :: qs ⟧ˢ in u 
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            |  ListType _ := (f, Array [seq Object (⟦ φ ++ merge_selection_sets (find_queries_with_label s f u.(type) qs) ⟧ˢ in v) | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label f qs ⟧ˢ in u;
            | NT _
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (f, Object (⟦ φ ++ merge_selection_sets (find_queries_with_label s f u.(type) qs) ⟧ˢ in v)) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u;
                
                | _ =>  (f, Leaf Null) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u
                }
            };

        | None => ⟦ qs ⟧ˢ in u (* Should throw error *)
        };

      execute_selection_set u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            |  ListType _ := (l, Array [seq Object (⟦ φ ++ merge_selection_sets (find_queries_with_label s l u.(type) qs) ⟧ˢ in v) | v <- neighbours_with_field g u (Field f α)])
                              :: ⟦ filter_queries_with_label l qs ⟧ˢ in u;
            | NT _
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (l, Object (⟦ φ ++ merge_selection_sets (find_queries_with_label s l u.(type) qs) ⟧ˢ in v)) :: ⟦ filter_queries_with_label l qs ⟧ˢ in u;
                
                | _ =>  (l, Leaf Null) :: ⟦ filter_queries_with_label l qs ⟧ˢ in u
                }
            };

        | None => ⟦ qs ⟧ˢ in u (* Should throw error *)
        }

    }
  where "⟦ queries ⟧ˢ 'in' u" := (execute_selection_set u queries).
  Proof.
    all: do [leq_queries_size].
  Qed.

  
  Ltac exec :=
    repeat
      match goal with
      | [ H : lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _]] => rewrite H /=
      | [ H : (fields _) _ = _ |- context [ (fields _) _]] => rewrite H /=

      | [|- context [ lookup_field_in_type _ _ _]] => lookup
      | [|- context [ ?u.(fields) ]] =>
        let Hv := fresh "Hv" in
        let v := fresh "v" in
        let vs := fresh "vs" in
        case Hv : (u.(fields) _) => [[v | vs] |] /=
      | [ H : does_fragment_type_apply _ _ _ = _ |- context [ does_fragment_type_apply _ _ _]] => rewrite H /=
      | [ |- context [ ⟦ _ ⟧ˢ in _ ] ] => simp execute_selection_set
      end.



  
 

   Lemma exec_frags_nil_func (f : Name -> seq (@Query Name Vals) -> seq Query) u ptys φ :
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u = [::].
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
    ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u = [::].
   Proof.
     by apply: (exec_frags_nil_func (fun t qs => qs)).
  Qed.
  
  Lemma exec_frags_nil_get_types u ty φ :
    u.(type) \notin get_possible_types s ty ->
    ⟦ [seq InlineFragment t φ | t <- get_possible_types s ty] ⟧ˢ in u = [::].
  Proof.
    by move=> Hnin; apply: exec_frags_nil => //=; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.



  Lemma exec_cat_frags_func (f : Name -> seq (@Query Name Vals) -> seq Query) ptys u φ1 φ2 :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \notin ptys ->
    ⟦ φ1 ++ [seq InlineFragment t (f t φ2) | t <- ptys] ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u.   
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
        congr cons; congr pair; congr Object.
        by rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.

      * rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        rewrite find_queries_with_label_cat find_map_inline_nil_func // cats0.
          by congr cons; congr pair; congr Array.

    - by apply: IH; leq_queries_size.

    - case fld.(return_type) => //= rty.
      * case ohead => [v|] //=; rewrite filter_queries_with_label_cat filter_map_inline_func Hinlineswap IH //; leq_queries_size.
        congr cons; congr pair; congr Object.
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
    ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- ptys] ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u.                                                            
  Proof.
    by apply: (exec_cat_frags_func (fun t qs => qs)).
  Qed.

  Lemma exec_cat_frags_get_types ty u φ1 φ2 :
    u.(type) \notin get_possible_types s ty ->
    ⟦ φ1 ++ [seq InlineFragment t φ2 | t <- get_possible_types s ty] ⟧ˢ in u =
     ⟦ φ1 ⟧ˢ in u.                                                                      
  Proof.
    by move=> Hnin; apply: exec_cat_frags => //; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
  Qed.
    

  
  Lemma exec_inlined_func (f : Name -> seq (@Query Name Vals) -> seq Query) ptys u φ :
    (forall rname t φ, filter_queries_with_label rname (f t φ) = f t (filter_queries_with_label rname φ)) ->
    uniq ptys ->
    all (is_object_type s) ptys ->
    u.(type) \in ptys ->
                 ⟦ [seq InlineFragment t (f t φ) | t <- ptys] ⟧ˢ in u =  ⟦ [:: InlineFragment u.(type) (f u.(type) φ) ] ⟧ˢ in u.
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
                 ⟦ [seq InlineFragment t φ | t <- ptys] ⟧ˢ in u =  ⟦ [:: InlineFragment u.(type) φ ] ⟧ˢ in u.
  Proof.
    by apply: (exec_inlined_func (fun t qs => qs)).
  Qed.

    


  Lemma reground_exec φ u :
    u \in g.(nodes) ->
    ⟦ reground s u.(type) φ ⟧ˢ in u =  ⟦ φ ⟧ˢ in u.
  Proof.    
    funelim (reground s u.(type) φ) => //=; do ? by exec.
    all: do ? [by intros; exec; rewrite filter_reground_swap filter_filter_absorb // H].
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty| rty] /=.
      * case Hv : ohead => [v|] //=;
        rewrite filter_reground_swap filter_filter_absorb // H0 // -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        congr cons; congr pair; congr Object.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbours_are_in_nodes.
        have Hvtype : v.(type) = rty.
        rewrite Hrty /= in Heq.
        apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field s3 f1) = Some f by [].
        move/ohead_in: Hv => Hin.
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s3 f1) f Hlook v Hin).
          by rewrite Hrty.
        by apply: H => //; rewrite Hvtype.
        
        
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        have Hvin : v \in g.(nodes).
        apply: neighbours_are_in_nodes; exact: Hin.
        have Hvtype : v.(type) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field s3 f1) = Some f by [].
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s3 f1) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
        by apply: H => //; rewrite Hvtype.
    
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty | rty] //=.
      * case Hv : ohead => [v|] /=; rewrite filter_reground_swap filter_filter_absorb // H0 //.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Object.
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
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s3 f1) f Heq0 v Hin).
          by rewrite Hrty.
        
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Object.
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

        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s3 f1) f Heq0 v Hin).
          by rewrite Hrty.
     

    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty| rty] /=.
      * case Hv : ohead => [v|] //=;
        rewrite filter_reground_swap filter_filter_absorb // H0 // -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        congr cons; congr pair; congr Object.
        have Hvin : v \in g.(nodes).
        apply: ohead_in_nodes; last by apply: Hv.
        apply/allP.
          by apply: neighbours_are_in_nodes.
        have Hvtype : v.(type) = rty.
        rewrite Hrty /= in Heq.
        apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field s5 f2) = Some f by [].
        move/ohead_in: Hv => Hin.
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s5 f2) f Hlook v Hin).
          by rewrite Hrty.
        by apply: H => //; rewrite Hvtype.
        
        
      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Object.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        rewrite Hrty /= in H.
        have Hvin : v \in g.(nodes).
        apply: neighbours_are_in_nodes; exact: Hin.
        have Hvtype : v.(type) = rty.
        rewrite Hrty in Heq; apply: (in_object_possible_types Heq).
        have Hlook : lookup_field_in_type s u.(type) (Field s5 f2) = Some f by [].
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s5 f2) f Hlook v Hin).
          by rewrite Hrty /=. (* ?? *)
        by apply: H => //; rewrite Hvtype.
    
    - move=> Huin; exec.
      case Hrty : f.(return_type) => [rty | rty] //=.
      * case Hv : ohead => [v|] /=; rewrite filter_reground_swap filter_filter_absorb // H0 //.
        rewrite -filter_reground_swap find_filter_nil.
        simp merge_selection_sets => /=; rewrite cats0.
        congr cons; congr pair; congr Object.
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
        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s5 f2) f Heq0 v Hin).
          by rewrite Hrty.


      * rewrite filter_reground_swap filter_filter_absorb // H0 //; congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Object.
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

        move: (@neighbours_are_subtype_of_field Name Vals s g u (Field s5 f2) f Heq0 v Hin).
          by rewrite Hrty.
  Qed.

  
  Lemma ground_queries_exec ty φ u :
    u \in g.(nodes) ->
    u.(type) \in get_possible_types s ty ->
                 ⟦ ground_queries s ty φ ⟧ˢ in u =  ⟦ φ ⟧ˢ in u.
  Proof.
    funelim (ground_queries s ty φ) => //= Huin Hin.
    - by have <- /= := (in_object_possible_types Heq Hin); apply: reground_exec.
    - have -> /= : ⟦ [seq InlineFragment t (reground s t queries) | t <- get_possible_types s type_in_scope] ⟧ˢ in u =  ⟦ [:: InlineFragment u.(type) (reground s u.(type) queries)] ⟧ˢ in u.
      apply: exec_inlined_func => //=.
      by apply: filter_reground_swap.
      by apply: uniq_get_possible_types.
      by apply/allP; apply: in_possible_types_is_object.
       
      exec.
      have -> /= : does_fragment_type_apply s u.(type) u.(type) by apply: object_applies_to_itself; apply: (in_possible_types_is_object Hin).
      rewrite cats0.
        by apply: reground_exec.
  Qed.
        
    


  Lemma exec_nil u φ2 :
    [::] = ⟦ φ2 ⟧ˢ in u -> forall φ : seq Query, ⟦ φ ⟧ˢ in u = ⟦ φ2 ++ φ ⟧ˢ in u.
  Proof.
    funelim ( ⟦ φ2 ⟧ˢ in u) => //=; intros; exec.
      by rewrite catA; apply: H.
  Qed.
    
  Lemma single_val_inv f v φ1 φ2 u :
    (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u = ⟦ φ2 ⟧ˢ in u ->
    [\/
     exists q (Hfield : q.(is_field)) φ2', [/\ lookup_field_in_type s u.(type) (qname q Hfield) = None,
               φ2 = q :: φ2' & ⟦ φ2' ⟧ˢ in u =  (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u],

       exists α φ2', φ2 = SingleField f α :: φ2' /\  ⟦ filter_queries_with_label f φ2' ⟧ˢ in u =  ⟦ φ1 ⟧ˢ in u,

     exists f' α φ2', φ2 = LabeledField f f' α :: φ2' /\  ⟦ filter_queries_with_label f φ2' ⟧ˢ in u =  ⟦ φ1 ⟧ˢ in u |
     exists t β φ2', [/\  φ2 = InlineFragment t β :: φ2' &
                 [\/ does_fragment_type_apply s u.(type) t /\
                  ⟦ β ++ φ2' ⟧ˢ in u = (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u |
                 does_fragment_type_apply s u.(type) t = false /\
                  ⟦ φ2' ⟧ˢ in u = (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u]]].
  Proof.
    elim: φ2 => //= q φ2 IH.
    case_query q; exec.
    all: do ? by move=> Heq; inversion Heq.
    - case=> -> _ Hexec.
      constructor 2.
      by exists α, φ2; split=> //=.
     
    - intros; constructor 1. 
      have Hfield : is_field (SingleField f0 α) by [].
        by exists (SingleField f0 α), Hfield, φ2; split=> //=.
    - by case=> <- Heq; constructor 3; exists f0, α, φ2; split => //=.
    - intros; constructor 1.
      have Hfield : is_field (LabeledField l f0 α) by [].
      exists (LabeledField l f0 α), Hfield, φ2; split=> //=.
    - case fld.(return_type) => rty /=; last by move=> Hcontr; inversion Hcontr.
        by case ohead => [v'|] Hcontr; inversion Hcontr.
    - intros; constructor 1.
      have Hfield : is_field (NestedField f0 α β) by [].
      exists (NestedField f0 α β), Hfield, φ2; split=> //=.
    - case fld.(return_type) => rty /=; last by move=> Hcontr; inversion Hcontr.
        by case ohead => [v'|] Hcontr; inversion Hcontr.   
    - intros; constructor 1.
      have Hfield : is_field (NestedLabeledField l f0 α β) by [].
      exists (NestedLabeledField l f0 α β), Hfield, φ2; split=> //=.

    - case Hfapplies: does_fragment_type_apply => /=; intros; constructor 4; exists t, β, φ2; split=> //=.
        * by constructor 1; split.
        * by constructor 2; split. 
  Qed.

  Lemma single_val_inv2 f v φ1 φ2 u :
    [\/
     exists q (Hfield : q.(is_field)) φ2', [/\ lookup_field_in_type s u.(type) (qname q Hfield) = None,
               φ2 = q :: φ2' & ⟦ φ2 ⟧ˢ in u =  (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u],

       exists α fld φ2', [/\ φ2 = SingleField f α :: φ2',
                 lookup_field_in_type s u.(type) f = Some fld,
                 (u.(fields) (Field f α)) = Some (inl v) &  
                 ⟦ filter_queries_with_label f φ2' ⟧ˢ in u =  ⟦ φ1 ⟧ˢ in u],

       exists f' α fld φ2', [/\ φ2 = LabeledField f f' α :: φ2',
                        lookup_field_in_type s u.(type) f' = Some fld,
                        (u.(fields) (Field f' α)) = Some (inl v) &  
                        ⟦ filter_queries_with_label f φ2' ⟧ˢ in u =  ⟦ φ1 ⟧ˢ in u] |
     exists t β φ2', [/\  φ2 = InlineFragment t β :: φ2' &
                 [\/ does_fragment_type_apply s u.(type) t /\
                  ⟦ β ++ φ2' ⟧ˢ in u = (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u |
                 does_fragment_type_apply s u.(type) t = false /\
                  ⟦ φ2' ⟧ˢ in u = (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u]]] ->
    (f, Leaf (SingleValue v)) :: ⟦ φ1 ⟧ˢ in u = ⟦ φ2 ⟧ˢ in u.
  Proof.
    case.
    - case=> q [Hfield [φ2' [Hlook -> Hexec]]]; case_query q => //=.
    - case=> α [fld [φ2' [-> Hlook Hv Hexec]]]; exec.
        by rewrite Hv /= Hexec.
    - case=> f' [α [fld [φ2' [-> Hlook Hv Hexec]]]]; exec.
        by rewrite Hv /= Hexec.
    - case=> t [β [φ2' [-> [[Hfapplies Hexec] | [HNapplies Hexec]]]]].
      * by exec; rewrite Hfapplies /= Hexec.
      *  by exec; rewrite Hexec.
  Qed.
     
  Lemma exec_cat_hd u φ1 φ2 :
    ⟦ φ1 ⟧ˢ in u =  ⟦ φ2 ⟧ˢ in u ->
    forall φ,
      ⟦ φ1 ++ φ ⟧ˢ in u =  ⟦ φ2 ++ φ ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n φ1 φ2  => /= [| n IH] φ1 φ2.
    - rewrite leqn0 => /queries_size_0_nil ->; apply: exec_nil.
    - case: φ1 => //= [| q φ1] ; first by intros; apply: exec_nil.
      case_query q; simp query_size => Hleq; exec.
    - intros.
      exec.
      rewrite Hv /=.
      move/single_val_inv: H; case.
      * case=> q [Hfield [φ2' [HNlook Heq Hexec]]].
        rewrite filter_queries_with_label_cat.
        case_query q => //= _ HNlook ->; exec; rewrite -/cat.
  Abort.


  Lemma empty_frags_exec ptys u φ :
    ⟦ [seq InlineFragment t [::] | t <- ptys] ++ φ ⟧ˢ in u = ⟦ φ ⟧ˢ in u.
  Proof.
    elim: ptys φ => //= t ptys IH φ; exec.
      by case does_fragment_type_apply => /=; apply: IH.
  Qed.

  Lemma frags_N_exec ty u φ :
    u.(type) \notin get_possible_types s ty ->
    forall q,
      ⟦ [seq InlineFragment t [:: q] | t <- get_possible_types s ty] ++ φ ⟧ˢ in u = ⟦ φ ⟧ˢ in u.
  Proof.
  Abort.
    

    
  

  
  Reserved Notation "ty '⊢' φ '≡' φ'" (at level 80). 
         
  Equations? Equiv  (ty : Name) (φ1 φ2 : seq (@Query Name Vals)) : bool by wf (queries_size φ1 + queries_size φ2) :=
    {
      _ ⊢ [::] ≡ [::] := true;

      ty ⊢ SingleField f α :: φ1 ≡ SingleField f' α' :: φ2
        with (f == f') && (α == α') :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };
      
       ty ⊢ SingleField f α :: φ1 ≡ LabeledField l f' α' :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

       ty ⊢ LabeledField l f α :: φ1 ≡ SingleField f' α' :: φ2
        with [&& (l == f'), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };
          
       ty ⊢ LabeledField l f α :: φ1 ≡ LabeledField l' f' α' :: φ2
        with [&& (l == l'), (f == f') & (α == α')] :=
        {
        | true 
            with lookup_field_in_type s ty f :=
            {
            | Some fld := ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2;
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        }; 

      ty ⊢ NestedField f α β :: φ1 ≡ NestedField f' α' χ :: φ2
        with (f == f') && (α == α') :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s f ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedField f α β :: φ1 ≡ NestedLabeledField l f' α' χ :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s f ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label f φ1 ≡ filter_queries_with_label f φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedLabeledField l f α β :: φ1 ≡ NestedField f' α' χ :: φ2
        with [&& (f == l), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s l ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s l ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      ty ⊢ NestedLabeledField l f α β :: φ1 ≡ NestedLabeledField l' f' α' χ :: φ2
        with [&& (l == l'), (f == f') & (α == α')] :=
        {
        | true
            with lookup_field_in_type s ty f :=
            {
            | Some fld := (all (fun t => t ⊢ β ++ merge_selection_sets (find_queries_with_label s l ty φ1) ≡
                                       χ ++ merge_selection_sets (find_queries_with_label s l ty φ2))
                             (get_possible_types s fld.(return_type))) &&
                             (ty ⊢ filter_queries_with_label l φ1 ≡ filter_queries_with_label l φ2);
            | _ := ty ⊢ φ1 ≡ φ2
            };
        | _ := false
        };

      (* ty ⊢ InlineFragment t1 β :: φ1 ≡ InlineFragment t2 χ :: φ2 *)
      (*   with does_fragment_type_apply s ty t1, does_fragment_type_apply s ty t2 := *)
      (*   { *)
      (*   | true | true := ty ⊢ β ++ φ1 ≡ χ ++ φ2; *)
      (*   | true | false := ty ⊢ β ++ φ1 ≡ φ2; *)
      (*   | false | true := ty ⊢ φ1 ≡ χ ++ φ2; *)
      (*   | _ | _ := ty ⊢ φ1 ≡ φ2 *)
      (*   }; *)
          
      ty ⊢ InlineFragment t β :: φ1 ≡ φ2
        with does_fragment_type_apply s ty t :=
        {
        | true := ty ⊢ β ++ φ1 ≡ φ2;
        | _ := ty ⊢ φ1 ≡ φ2
        };
      
      ty ⊢ φ1 ≡ InlineFragment t β :: φ2
        with does_fragment_type_apply s ty t :=
        {
        | true := ty ⊢ φ1 ≡ β ++ φ2;
        | _ := ty ⊢ φ1 ≡ φ2
        };
         
      _ ⊢ _ ≡ _ := false
    }
  where "ty '⊢' φ1 '≡' φ2" := (Equiv ty φ1 φ2).
  Proof.
    all: do [leq_queries_size].

    all: do ?[ by have Hfleq := (found_queries_leq_size s f ty φ1);
               have Hmleq := (merged_selections_leq (find_queries_with_label s f ty φ1)); 
                            leq_queries_size].
    all: do ? [have Hfleq := (found_queries_leq_size s l ty φ1);
               have Hmleq := (merged_selections_leq (find_queries_with_label s l ty φ1));
                            leq_queries_size].  
  Qed.

  
  Ltac equiv :=
    repeat match goal with
           | [ H: ?eq1 && ?eq2 = _ |- context [_ && _]] => rewrite H /=
           | [ H: lookup_field_in_type _ _ _ = _ |- context [ lookup_field_in_type _ _ _ ]] => rewrite H /=
           | [ H:  does_fragment_type_apply _ _ _ = _ |- context [does_fragment_type_apply _ _ _]] =>
               rewrite H /=
           | [ H:  is_true (does_fragment_type_apply _ _ _) |- context [does_fragment_type_apply _ _ _]] =>
               rewrite H /=
           | [|- context [ Equiv _ _ _ ]] => simp Equiv
           end.
  
  
  Lemma equiv_eval1 ty φ1 φ2 :
    (forall t, t \in get_possible_types s ty ->
                t ⊢ φ1 ≡ φ2) ->
    forall u, u.(type) \in get_possible_types s ty ->
                      ⟦ φ1 ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u.
  Proof.
    move=> Heq u Hin.
    move: (Heq _ Hin).
    funelim (Equiv _  φ1 φ2) => //=.
  Qed.

               
  Lemma equiv_eval2 u φ1 φ2 :
    u.(type) ⊢ φ1 ≡ φ2 ->
    ⟦ φ1 ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u.
  Proof.
    funelim (_ ⊢ φ1 ≡ φ2) => //=.
  Qed.


  Reserved Notation "ty '⊢' φ '≡p' φ'" (at level 80). 

  Inductive EquivP (ty : Name) : seq Query -> seq (@Query Name Vals) -> Prop :=
  | ENil : ty ⊢ [::] ≡p [::]
              
  | ESF1 : forall f α φ φ',
      ty ⊢ filter_queries_with_label f φ ≡p filter_queries_with_label f φ'  ->
      ty ⊢ SingleField f α :: φ ≡p SingleField f α :: φ' 

  | ESF2 : forall f α φ φ',
      ty ⊢ φ ≡p  φ'  ->
      ty ⊢ SingleField f α :: φ ≡p φ' 

 
  | ENF1 : forall f α β χ fld φ φ',
      lookup_field_in_type s ty f = Some fld ->
      (forall t, t \in get_possible_types s fld.(return_type) ->
                  t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ) ≡p
                    χ ++ merge_selection_sets (find_queries_with_label s f ty φ')) ->
      
      ty ⊢ filter_queries_with_label f φ ≡p filter_queries_with_label f φ' ->
      ty ⊢ NestedField f α β :: φ ≡p NestedField f α χ :: φ' 

  | ENF2 : forall f α β φ φ',
      lookup_field_in_type s ty f = None ->
      ty ⊢ φ ≡p φ' ->
      ty ⊢ NestedField f α β :: φ ≡p φ' 

  | EIF11 : forall t β φ φ',
      does_fragment_type_apply s ty t ->
      ty ⊢ β ++ φ ≡p φ'  ->
      ty ⊢ InlineFragment t β :: φ ≡p φ' 

  | EIF12 : forall t β φ φ',
      does_fragment_type_apply s ty t ->
      ty ⊢ φ' ≡p β ++ φ  ->
      ty ⊢ φ' ≡p InlineFragment t β :: φ 
         
  | EIF21 : forall t β φ φ',
      does_fragment_type_apply s ty t = false ->
      ty ⊢ φ ≡p φ'  ->
      ty ⊢ InlineFragment t β :: φ ≡p φ' 

  | EIF22 : forall t β φ φ',
      does_fragment_type_apply s ty t = false ->
      ty ⊢ φ' ≡p φ  ->
      ty ⊢ φ' ≡p  InlineFragment t β :: φ
  where "ty '⊢' φ '≡p' φ'"  := (EquivP ty φ φ').


  Lemma equivP ty φ1 φ2 :
    reflect (ty ⊢ φ1 ≡p φ2) (ty ⊢ φ1 ≡ φ2).
  Abort.








  Lemma equiv_sym ty φ1 φ2 :
    (ty ⊢ φ1 ≡ φ2) = (ty ⊢ φ2 ≡ φ1).
  Proof.
    funelim (ty ⊢ φ1 ≡ φ2) => //=; equiv.    
    - by rewrite eq_sym [f0 == f]eq_sym; equiv.
      all: do ? [rewrite eq_sym [f0 == f]eq_sym; equiv;
                 case/andP: Heq0 => [/eqP Hfeq _]; rewrite -Hfeq Heq /=;
                   by apply: H].
    - by rewrite eq_sym [s3 == s0]eq_sym [f1 == f]eq_sym Heq /=.
    - rewrite eq_sym [s3 == s0]eq_sym [f1 == f]eq_sym Heq0 /=.
        by case/and3P: Heq0 => [/eqP <- /eqP <- _]; rewrite Heq /= H.
    - rewrite eq_sym [s3 == s0]eq_sym [f1 == f]eq_sym Heq0 /=.
        by case/and3P: Heq0 => [/eqP <- /eqP <- _]; rewrite Heq /= H.
    - by rewrite eq_sym [s0 == s2]eq_sym [f == f0]eq_sym Heq /=.
    - by rewrite eq_sym [f2 == f1]eq_sym; equiv.
    - rewrite eq_sym [f2 == f1]eq_sym; equiv.
      case/andP: Heq0 => [/eqP Hfeq _]; rewrite -Hfeq Heq /=.
      (* move=> /andP [Hall Hfilter]. *)
      (* apply_andP. *)
      congr andb; last by rewrite H0.
      elim: get_possible_types => //= t ptys IH'.
      rewrite H; congr andb.
      by rewrite IH'.
      
    - rewrite eq_sym [f2 == f1]eq_sym; equiv.
      case/andP: Heq0 => [/eqP Hfeq _]; rewrite -Hfeq Heq /=.
        by apply: H.
  Qed.
  



    
  Lemma equiv_fragment_true t β ty φ1 φ2 :
    does_fragment_type_apply s ty t ->
    ty ⊢ InlineFragment t β :: φ1 ≡ φ2 ->
    ty ⊢ β ++ φ1 ≡ φ2.
  Proof.
    elim: φ2 => //= [| q φ2 IH].
    - by equiv => -> /=.
    - case: q => /= [f α | | f α χ | | t' χ] Hfapplies; equiv; do ? by rewrite Hfapplies /=.
      admit. (* Labeled *)
      admit. (* Labeled *)
  Admitted.


   Lemma equiv_fragment_inv t β ty φ1 φ2 :
    does_fragment_type_apply s ty t = false ->
    (ty ⊢ InlineFragment t β :: φ1 ≡ φ2) = (ty ⊢ φ1 ≡ φ2).
   Proof.
     move: {2}(queries_size _ + queries_size _) (leqnn (queries_size φ2 + queries_size (InlineFragment t β :: φ1))) => n.
     elim: n φ2 φ1 t β => /= [| n IH] φ2 φ1 t β.
     - admit.
     - Abort.
       
    
  Lemma equiv_fragment_inv t β ty φ1 φ2 :
    does_fragment_type_apply s ty t ->
    (ty ⊢ InlineFragment t β :: φ1 ≡ φ2) = (ty ⊢ β ++ φ1 ≡ φ2).
  Proof.
    move: {2}(queries_size _ + queries_size _) (leqnn (queries_size φ2 + queries_size (InlineFragment t β :: φ1))) => n.
    elim: n φ2 φ1 t β => /= [| n IH] φ2 φ1 t β.
    admit.
    case: φ2 => //= [| q φ2]; first by intros; equiv.
    case_query q => //=; simp query_size => Hleq Hfapplies; equiv => //.
    case Hfapplies2 : does_fragment_type_apply => /=.
    rewrite [RHS]equiv_sym.
    rewrite [RHS]IH //.
    by rewrite equiv_sym.
    leq_queries_size.
    
    rewrite [RHS]equiv_sym IH //.
    rewrite equiv_sym.
    
  Abort.

 
  (* Ok - only missing labeled cases *)
  Lemma equiv_refl ty φ :
    ty ⊢ φ ≡ φ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => /= [| n IH] ty φ; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
    case: φ => //= q φ.
    case_query q; simp query_size => Hleq; equiv.
    - case: eqP => //= _; case: eqP => //= _.
      lookup => //=; last by apply: IH.
        by apply: IH; leq_queries_size.
    
    - admit. (* Labeled *)
    - case: eqP => //= _; case: eqP => //= _.
      lookup => //=; last by apply: IH; leq_queries_size.
      apply_andP; last by apply: IH; leq_queries_size.
      by elim: get_possible_types => //= t ptys IH'; apply_andP; apply: IH; leq_queries_size.

    - admit. (* Labeled *)

    - case does_fragment_type_apply => //=; apply: IH; leq_queries_size.
        
  Admitted.
 
  Hint Resolve equiv_refl.
  
  Lemma equiv_cat_hd ty φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    forall φ,
      ty ⊢ φ1 ++ φ ≡ φ2 ++ φ.
  Proof.
    funelim (ty ⊢ φ1 ≡ φ2) => //=; equiv.
    - intros; equiv.


 
    
  Lemma equiv_trans t φ1 φ2 φ3 :
    t ⊢ φ1 ≡ φ2 ->
    t ⊢ φ2 ≡ φ3 ->
    t ⊢ φ1 ≡ φ3.
  Proof.
    
  Admitted.
        

  Lemma filter_preserves_equiv rname ty φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ filter_queries_with_label rname φ1 ≡ filter_queries_with_label rname φ2.
  Proof.
    funelim (_ ⊢ φ1 ≡ _) => //=. 
    - simp filter_queries_with_label; equiv; rewrite -filter_queries_with_label_cat; apply: H.
    - simp filter_queries_with_label; equiv; apply: H.
    - case/andP: Heq0 => [/eqP <- /eqP Hfeq].
      simp filter_queries_with_label.
      case: eqP => //= [ -> | Hneq] //.
      equiv; case: eqP => //= _; case: eqP => //= _.
      rewrite Heq /= => Hequiv.
        by rewrite filter_swap // [X in _ ⊢ _ ≡ X]filter_swap //; apply: H.
    - case/andP: Heq0 => [/eqP <- /eqP Hfeq].      
      simp filter_queries_with_label.
      case: eqP => //= [ _| Hneq] //; first by apply: H.
      equiv; case: eqP => //= _; case: eqP => //= _.
      by rewrite Heq /= => Hequiv; apply: H.

    - rewrite filter_queries_with_label_equation_6. case: eqP => //= Hfeq; equiv.
      
      (* Fragments again... *)
  Admitted.



    

 
      
      
  Lemma equiv_frag_E t β ty φ1 φ2 :
    does_fragment_type_apply s ty t = false ->
    (ty ⊢ φ1 ≡ InlineFragment t β :: φ2) =
    (ty ⊢ φ1 ≡ φ2).
  Proof.
    move=> Hfapplies.
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n φ1 => /= [| n IH] φ1; first by rewrite leqn0 => /queries_size_0_nil ->; equiv.
    case: φ1 => /= [| q φ1]; equiv => //.
    case: q; intros; equiv => //=.
    case Hfapplies2 : does_fragment_type_apply => //=; equiv;
    apply: IH; simp query_size in leqnn; leq_queries_size.
  Qed.

  Lemma filter_ground_swap rname φ t ty :
    t \in get_possible_types s ty ->    
          t ⊢ filter_queries_with_label rname (ground s ty φ) ≡ ground s ty (filter_queries_with_label rname φ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ t rname => /= [| n IH] φ t rname; first by rewrite leqn0 => /queries_size_0_nil ->; equiv.
    case: φ => /= [| q φ]; equiv => //.
    case_query q; simp query_size => Hleq Hin.
    - simp ground; case Hscope : is_object_type => /=.
      * simp filter_queries_with_label => /=; case: eqP => //= [Heq | Hneq] //=; first by apply: IH.
        simp ground; rewrite Hscope /=.
        equiv; case: eqP => //= _; case: eqP => //= _.
        lookup => /=.
        apply: filter_preserves_equiv.
        apply: IH => //=.
        apply: IH => //=.
      * 
        
        
  Abort.

      
      
                  
  Lemma ground_equiv t φ1 φ2 :
    t ⊢ φ1 ≡ φ2 ->
    forall ty,
      t \in get_possible_types s ty ->
            t ⊢ ground s ty φ1 ≡ φ2.
  Proof.      
    funelim (t ⊢ φ1 ≡ φ2) => //=.
    - by intros; simp ground; equiv.
    - by intros; simp ground; equiv.
    - intros; simp ground.
      case Hscope : is_object_type => /=; equiv.
      * admit.
      * admit.
    - intros; simp ground.
      case Hscope : is_object_type => /=; equiv.
      admit.

    - intros; simp ground.
      case Hscope : is_object_type => /=; equiv.
      rewrite -ground_clause_2_equation_1 -Hscope.
      rewrite -ground_equation_2.
      by apply: H.
    - admit.
    - by intros; rewrite equiv_frag_E //; apply: H.

    - admit.
    - admit.

    - move=> /andP [Hall Hfeq] t Hin.
      simp ground.
      lookup => /=.
      case Hscope : is_object_type => /=; equiv.
      apply_andP.
      case get_possible_types => //= rty Hrtyin; apply_andP.
      apply: equiv_trans.
      apply: equiv_un
      
      case: eqP => /=

      rewrite Heq.
      
      
               
  Lemma equiv_eval u φ1 φ2 :
      Equiv u.(type) φ1 φ2 ->
      ⟦ φ1 ⟧ˢ in u = ⟦ φ1 ⟧ˢ in u.
  Proof.
    funelim (Equiv _  φ1 φ2) => //=.
    
               
  
  Inductive Equiv (ty : Name) : seq Query -> seq (@Query Name Vals) -> Prop :=
  | ENil : ty ⊢ [::] ≡ [::]
              
  | ESF : forall f α φ φ',
      ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ'  ->
      ty ⊢ SingleField f α :: φ ≡ SingleField f α :: φ' 
         
 
  | ENF : forall f α β χ fld φ φ',
      lookup_field_in_type s ty f = Some fld ->
      (forall t, t \in get_possible_types s fld.(return_type) ->
                  t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ) ≡
                    χ ++ merge_selection_sets (find_queries_with_label s f ty φ')) ->
      
      ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ' ->
      ty ⊢ NestedField f α β :: φ ≡ NestedField f α χ :: φ' 

  | EIF11 : forall t β φ φ',
      does_fragment_type_apply s ty t ->
      ty ⊢ β ++ φ ≡ φ'  ->
      ty ⊢ InlineFragment t β :: φ ≡ φ' 

  | EIF12 : forall t β φ φ',
      does_fragment_type_apply s ty t ->
      ty ⊢ φ' ≡ β ++ φ  ->
      ty ⊢ φ' ≡ InlineFragment t β :: φ 
         
  | EIF21 : forall t β φ φ',
      does_fragment_type_apply s ty t = false ->
      ty ⊢ φ ≡ φ'  ->
      ty ⊢ InlineFragment t β :: φ ≡ φ' 

  | EIF22 : forall t β φ φ',
      does_fragment_type_apply s ty t = false ->
      ty ⊢ φ' ≡ φ  ->
      ty ⊢ φ' ≡  InlineFragment t β :: φ 

      
  where "ty '⊢' φ '≡' φ' " := (Equiv ty φ φ').

  
  Hint Constructors Equiv.


  

  Hint Resolve filter_preserves_definition.
  
  Theorem equiv_eval ty φ1 φ2 :
    forall t, t \in get_possible_types s ty ->
               t ⊢ φ1 ≡ φ2 ->
               are_defined s φ1 t ->
               are_defined s φ2 t ->
               forall u,
                 u.(type) = t ->
                 ⟦ φ1 ⟧ˢ in u = ⟦ φ2 ⟧ˢ in u.
  Proof.
    move=> t Hin.
    elim=> //=.
    - intros; exec.
      rewrite H3.
      field_defined.
        by case (u.(fields) _) => [[v | vs] |] /=; rewrite H0 //; apply: filter_preserves_definition.
        
    - intros; simp execute_selection_set.
      rewrite H6 H /=.
      case fld.(return_type) => rty /=.
      * case ohead => [v|] /=; last by rewrite H3 //; apply: filter_preserves_definition; field_defined.
        rewrite H3 //; do ? by apply: filter_preserves_definition; field_defined.
        rewrite H6 (H1 v.(type)) //.
        admit.
        rewrite are_defined_cat; 
        admit. (* defined recursively... *)
        admit. (* defined recursively... *)
        
      * congr cons; last by rewrite H3 //; apply: filter_preserves_definition; field_defined.
        congr pair; congr Array; apply/eq_in_map=> v Hvin; congr Object.
        rewrite H6; apply: (H1 v.(type)) => //=.
        admit.
        admit. (* defined_recursively... *)
        admit. (* defined_recursively... *)
        
    - intros; exec. 
      rewrite H4; exec.
      apply: H1 => //=.
      rewrite -H4 in H2 *.
      move: H2; simp are_defined; case/andP=> *; rewrite are_defined_cat.
      apply_andP.
      admit. (* defined in supertyp
    - intros; simp execute_selection_set.
      by rewrite H2 H /=; apply: H1.

    - by intros; simp execute_selection_set; rewrite H2 H /=; apply: H1.
    - by intros; simp execute_selection_set; rewrite H2 H /=; apply: H1.
  
  Admitted.


    
  Lemma equiv_sym ty φ φ' :
    ty ⊢ φ ≡ φ' ->
    ty ⊢ φ' ≡ φ.
  Proof.
    elim; intros; do ? by constructor.
    - by apply: (ENF _ _ _ _ _ fld) => //=.
    - by apply: EIF22 => //=.
    - by apply: EIF21 => //=.
  Qed.

  Hint Resolve equiv_sym.

  Hint Resolve queries_size_cat.
  Lemma equiv_refl ty φ :
    ty ⊢ φ ≡ φ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => //= [| n IH] ty φ; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
    case: φ; first by intros; constructor.
    case=> //= [f α | | f α β | | t β] φ; simp query_size => Hleq.
    - constructor; apply: IH; by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.

    - admit. (* Label *)

    (* - case Hlook : (lookup_field_in_type s ty f) => [fld|] //=; apply: ENF1. | apply: ENF2 => //]. *)
    (*   * exact: Hlook. *)
    (*   * move=> t Hin. *)
    (*     apply: IH => /=. *)
    (*     rewrite queries_size_cat. *)
    (*     admit. (* leq size *) *)
    (*     apply: IH. *)
    (*     admit. (* leq size *) *)
    (*   * apply: IH; ssromega. *)

    (* - admit. (* Labeled *) *)

    (* - case Hspread : (does_fragment_type_apply s ty t) => //=; [apply: EIF11 => //= | apply: EIF21 => //=]. *)
    (*   * apply: equiv_sym. *)
    (*     apply: EIF11 => //=. *)
    (*     apply: IH => //=. *)
    (*     rewrite queries_size_cat; ssromega. *)

    (*   * apply: equiv_sym. *)
    (*     apply: EIF21 => //=; apply: IH; ssromega. *)
  Admitted.

  Hint Resolve equiv_refl.
    

  Lemma equiv_trans ty φ1 φ2 φ3 :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ φ2 ≡ φ3 ->
    ty ⊢ φ1 ≡ φ3.
  Proof.
  Admitted.

  

  Lemma equiv_cat_hd ty φ1 φ1' :
    ty ⊢ φ1 ≡ φ1' ->
    forall φ,
      ty ⊢ φ1 ++ φ ≡ φ1' ++ φ.
  Proof.
    elim=> //=.
    - intros; constructor.
      by rewrite !filter_queries_with_label_cat; apply: H0.

    - intros; apply: (ENF _ _ _ _ _ fld) => //=.
      * move=> t Htin.
        rewrite !find_queries_with_label_cat !merge_selection_sets_cat !catA.
        by apply: H1 => //=.
      * by rewrite !filter_queries_with_label_cat; apply: H3.

    - by intros; apply: EIF11 => //=; rewrite catA; apply: H1.

    - by intros; apply: EIF12 => //=; rewrite catA; apply: H1.

    - by intros; apply: EIF21.

    - by intros; apply: EIF22.
  Qed.

  
 
  
  Lemma empty_frag_equiv_nil ty tys :
    ty ⊢ [seq InlineFragment t [::] | t <- tys] ≡ [::].
  Proof.
    elim: tys => //= t tys IH.
    case Hfapplies : (does_fragment_type_apply s ty t) => /=; [by apply: EIF11 | by apply: EIF21].
  Qed.

  
  Lemma inline_simple_field_is_equiv ptys ty f α :
    is_object_type s ty ->
    ty \in ptys ->
           ty ⊢ [seq InlineFragment t [:: SingleField f α] | t <- ptys] ≡ [:: SingleField f α].
  Proof.
    elim: ptys => //= t ptys IH Hscope.
    rewrite inE => /orP [/eqP Heq | Hin].
    - rewrite -Heq.
      apply: EIF11 => /=.
      * by apply: (object_applies_to_itself ty Hscope).
      * apply: ESF => /=.
        rewrite filter_frag; simp filter_queries_with_label => //=.
        by apply: empty_frag_equiv_nil.
        by apply_andP; apply/eqP.

    - case Hfapplies : (does_fragment_type_apply s ty t) => //=.
      apply: EIF11 => //=.
      apply: ESF => /=.
      rewrite filter_frag; simp filter_queries_with_label => //=.
      apply: empty_frag_equiv_nil.
      apply_andP.

      * apply: EIF21 => //=.
          by apply: IH.
  Qed.
  
  Lemma filter_inlined_query_are_empty_fragments rname tys :
    forall (q : @Query Name Vals) (Hfield : q.(is_field)),
      (qresponse_name q Hfield) = rname ->
      filter_queries_with_label rname [seq InlineFragment t [:: q] | t <- tys] =
      [seq InlineFragment t [::] | t <- tys].
  Admitted.

  Lemma filter_inline_query_id rname tys :
    forall (q : @Query Name Vals) (Hfield : q.(is_field)),
      (qresponse_name q Hfield) <> rname ->
      filter_queries_with_label rname [seq InlineFragment t [:: q] | t <- tys] =
      [seq InlineFragment t [:: q] | t <- tys].
  Admitted.

   Lemma filter_preserves_equiv ty φ φ' :
    ty ⊢ φ ≡ φ' ->
    forall f,
      ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ'.
  Proof.
    elim=> //=; intros; simp filter_queries_with_label.
    
    - case: eqP => /= [<- | Hneq] //=.
      constructor.
      rewrite filter_swap //.
      by rewrite [X in _ ⊢  _ ≡ X]filter_swap.

      
    - case: eqP => /= [<- | Hneq] //.
      apply: (ENF _ _ _ _ _ fld) => //=.
      * move=> t Hin.
        move/eqP/negbTE in Hneq.
        rewrite !find_filter_swap //.
          by apply: H0 => //=.
      * rewrite filter_swap //.
        by rewrite [X in _ ⊢  _ ≡ X]filter_swap.

    - by apply: EIF11 => //=; rewrite -filter_queries_with_label_cat; apply: H1.

    - by apply: EIF12 => //=; rewrite -filter_queries_with_label_cat; apply: H1.

    - by apply: EIF21.
    - by apply: EIF22.
  Qed.
  
 
    
  
   Lemma filter_remove_swap k (qs : seq (@Query Name Vals)) :
    filter_queries_with_label k (remove_redundancies qs) = remove_redundancies (filter_queries_with_label k qs).
  Admitted.


 

  Lemma find_queries_or_fields_is_same_if_all_fields ty label qs :
    all (fun q => q.(is_field)) qs ->
    find_queries_with_label s label ty qs = find_fields_with_response_name label qs.
  Proof.
    elim: qs => //= q qs IH /andP [Hfield Hfields].
    case: q Hfield => //= [f α | l f α | f α φ | l f α φ] _.

    all: do ?[by simp find_queries_with_label; simp find_fields_with_response_name;
              case: eqP => //= _; [congr cons |]; apply: IH].
  Qed.
  
 

 
   
  Lemma find_preserves_equiv ty f φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ find_queries_with_label s f ty φ1 ≡ find_queries_with_label s f ty φ2.
  Proof.
    elim=> //=.
    - intros; simp find_queries_with_label; case: eqP => //= [<- | Hneq].
      * constructor.
        by rewrite 2!filter_find_nil; constructor.
      * move/eqP/negbTE in Hneq; rewrite eq_sym in Hneq. 
        rewrite -(find_filter_swap s _ _ Hneq) //.
          by rewrite -[X in _ ⊢ _ ≡ X](find_filter_swap _ _ _ Hneq).

    - intros; simp find_queries_with_label; case: eqP => //= [<- | Hneq].

      * apply: (ENF _ _ _ _ _ fld) => //=.
        move=> t Hin.
        rewrite 2!find_absorb.
        apply: H0 => //=.
        by rewrite 2!filter_find_nil; constructor.
        
      * move/eqP/negbTE in Hneq; rewrite eq_sym in Hneq. 
        rewrite -(find_filter_swap _ _ _ Hneq) //.
          by rewrite -[X in _ ⊢ _ ≡ X](find_filter_swap _ _ _ Hneq).

    - intros; simp find_queries_with_label; rewrite H /=; by rewrite -find_queries_with_label_cat; apply: H1.
    - intros; simp find_queries_with_label; rewrite H /=; by rewrite -find_queries_with_label_cat; apply: H1.
    - intros; simp find_queries_with_label; rewrite H /=; apply: H1. 
    - intros; simp find_queries_with_label; rewrite H /=; apply: H1. 
  Qed.

  
  
  Lemma merge_ground_swap ty fld φ :
    is_object_type s ty ->
    all (fun q => if q.(oqname) is Some name then
                 lookup_field_in_type s ty name == Some fld
               else
                 false) φ ->
    merge_selection_sets (ground s ty φ) = ground s fld.(return_type) (merge_selection_sets φ).
  Proof.
    move=> Hscope.
    elim: φ fld => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH fld /andP  /=; last by case.

    - move=> [Hlook Hall]; simp ground; rewrite Hscope /=; simp merge_selection_sets => /=.
    - move=> [Hlook Hall]; simp ground; rewrite Hscope /=; simp merge_selection_sets => /=.

    - move=> [/eqP Hlook Hall]; simp ground; rewrite Hlook /= Hscope /=; simp merge_selection_sets => /=.
      rewrite ground_cat (IH fld) //=.
    - move=> [/eqP Hlook Hall]; simp ground; rewrite Hlook /= Hscope /=; simp merge_selection_sets => /=.
      rewrite ground_cat (IH fld) //=.
  Qed.




      
  
      
  Lemma filter_preserves_equivalent rname (φ : seq (@Query Name Vals)) :
    forall q1 (Hfield : q1.(is_field)),
      (qresponse_name q1 Hfield) != rname ->
      all (are_equivalent q1) φ ->
      all (are_equivalent q1) (filter_queries_with_label rname φ).
  Proof.
    apply_funelim (filter_queries_with_label rname φ) => //=; clear rname φ.
    - move=> rname t β φ IHsq IH q1 Hfield Hneq; case/andP.
      rewrite /are_equivalent /=; simp is_simple_field_selection; simp is_nested_field_selection.
      by rewrite 2!andbF orbF /=.

  Admitted.
      
      
  Lemma filter_preserves_merging f ty φ :
    is_field_merging_possible s ty φ ->
    is_field_merging_possible s ty (filter_queries_with_label f φ).
  Proof.
    funelim (is_field_merging_possible s ty φ) => //=.
    - move=> /andP [Hequiv Hmerge].
      simp filter_queries_with_label => /=; case: eqP => //= [<- | Hneq] //=.
      simp is_field_merging_possible; rewrite Heq /=.
      apply_andP.
      by rewrite find_filter_swap //; apply/eqP. 
      by rewrite filter_swap //; apply: H.

    - move=> /andP [Hequiv Hmerge].
      simp filter_queries_with_label => /=; case: eqP => //= [<- | Hneq] //=.
      simp is_field_merging_possible; rewrite Heq /=.
      apply_andP.
      admit. (* find fields swap with filter *)
        by rewrite filter_swap //; apply: H.

    - admit. (* Labeled *)
    - admit. (* Labeled *)
   
    - move=> /and3P [Hequiv Hsmerge Hmerge].
      simp filter_queries_with_label => /=; case: eqP => //= [<- | Hneq] //=.
      simp is_field_merging_possible; rewrite Heq0 /= Heq /=.
      apply_and3P.
      * by rewrite find_filter_swap //; apply/eqP.
      * by rewrite find_filter_swap //; apply/eqP.
      * by rewrite filter_swap //; apply: H0.

    - move=> /and3P [Hequiv Hsmerge Hmerge].
      simp filter_queries_with_label => /=; case: eqP => //= [<- | Hneq] //=.
      simp is_field_merging_possible; rewrite Heq0 /= Heq /=.
      apply_and3P.
      * admit. (* find fields swap with filter *)
      * admit. (* Same *)
      * by rewrite filter_swap //; apply: H0.

    - admit. (* Labeled *)
    - admit. (* Labeled *)

    - by simp filter_queries_with_label; simp is_field_merging_possible; rewrite Heq /=; apply: H.
    - by simp filter_queries_with_label; simp is_field_merging_possible; rewrite Heq0 /= Heq /= -filter_queries_with_label_cat; apply: H.
    - case/andP=> *; simp filter_queries_with_label; simp is_field_merging_possible; rewrite Heq0 /= Heq /= -filter_queries_with_label_cat.
      apply_andP; first by apply: H.
      by apply: H0.    
  Admitted.

  
  Lemma equiv_cat_tail ty φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    is_field_merging_possible s ty φ1 ->
    is_field_merging_possible s ty φ2 ->
    forall φ,
    ty ⊢ φ ++ φ1 ≡ φ ++ φ2.
  Proof.
    elim=> //=.
    - intros.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ φ1 φ2 => //= [| n IH] ty φ φ1 φ2; first by rewrite leqn0 => /queries_size_0_nil ->; rewrite 2!cat0s.
    case: φ => //=; case=> [f α | | f α β | | t β] φ; simp query_size => /= Hleq Heq Hmerge1 Hmerge2.
    - apply: ESF.
      rewrite 2!filter_queries_with_label_cat.
      apply: IH.
      by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        by apply: filter_preserves_equiv.
          by apply: filter_preserves_merging.
            by apply: filter_preserves_merging.

            
    - admit. (* label *)

    - case Hlook : (lookup_field_in_type s ty f) => [fld|] /=.
      apply: (ENF _ _ _ _ _ fld) => //=.
      * move=> t Hin.
        rewrite 2!find_queries_with_label_cat 2!merge_selection_sets_cat.
        rewrite !catA.
        apply: IH.
        have Hfeq1 := (found_queries_leq_size s f ty φ).
        have Hfeq2 := (merged_selections_leq (find_queries_with_label s f ty φ)).
          by rewrite queries_size_cat; ssromega.

        apply: (collect_preserves_equiv _ _ _ _ f fld) => //=.
        apply: (collect_preserves_merging _ _ _ f fld) => //=.
        apply: (collect_preserves_merging _ _ _ f fld) => //=.

      * rewrite !filter_queries_with_label_cat.
        apply: IH.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        by apply: filter_preserves_equiv.
        by apply: filter_preserves_merging.
          by apply: filter_preserves_merging.


    - admit. (* lookup = ⊥ *)

    - admit. (* Labeled *)

    - case Hfapplies : (does_fragment_type_apply s ty t) => //=.

      * apply: EIF11 => //=.
        apply: EIF12 => //=.
        rewrite !catA.
        apply: IH => //=.
        by rewrite queries_size_cat.


      * apply: EIF21 => //=.
        apply: EIF22 => //=.
        apply: IH => //=; ssromega.
  Admitted.


   Lemma filter_ground_swap_equiv k ty qs :
    forall t,
      t \in get_possible_types s ty ->
            t ⊢ filter_queries_with_label k (ground s ty qs) ≡ ground s ty (filter_queries_with_label k qs).
  Proof.
    elim: qs ty => //= q qs IH ty t Hin.
    case: q => [f α | | f α β | | t' β].
    - simp filter_queries_with_label; case: eqP => //= [Heq | Hneq].
      * rewrite Heq in IH *.
        simp ground; case Hscope : is_object_type => /=.
        + simp filter_queries_with_label => /=; case: eqP => //= _.
            by apply: IH.
        + rewrite filter_queries_with_label_cat filter_inlined_query_are_empty_fragments //.
          apply: equiv_trans.
          apply: equiv_cat_hd.
          apply: empty_frag_equiv_nil.
          by rewrite cat0s; apply: IH.

      * simp ground; case Hscope : is_object_type => /=.
        + simp filter_queries_with_label; case: eqP => //= _.
          by apply: ESF => //=; apply: filter_preserves_equiv; apply: IH => //=.
        + rewrite filter_queries_with_label_cat filter_inline_query_id.
          apply: equiv_cat_tail.
      simp ground.
    
    
    apply_funelim (ground s ty qs) => //=; clear ty.
    - intros; simp filt
    apply_fun
    

  
  Lemma is_merging_possible_in_subtype ty φ :
    is_field_merging_possible s ty φ ->
    forall t, t \in get_possible_types s ty ->
               is_field_merging_possible s t φ.
  Proof.
    funelim (is_field_merging_possible s ty φ) => //=.
    - move=> /andP [Hequiv Hmerge] t Hin.
      have Hteq := (in_object_possible_types Heq Hin).
      rewrite Hteq.
      simp is_field_merging_possible; rewrite Heq /=.
      apply_andP.

    - move=> /andP [Hequiv Hmerge] t Hin.
      have Hobj := (in_possible_types_is_object Hin).
      simp is_field_merging_possible; rewrite Hobj /=.
      apply_andP; [| by apply: H].
      admit.

    - admit. (* Labeled *)
    - admit. (* Labeled *)

    - move=> /and3P [Hequiv Hsubmerge Hmerge] t Hin.
      have Hteq := (in_object_possible_types Heq Hin).
      by rewrite Hteq; simp is_field_merging_possible; rewrite Heq0 /= Heq /=; apply_and3P.
    - move=> /and3P [Hequiv Hsubmerge Hmerge] t Hin.
      have Hobj := (in_possible_types_is_object Hin).
      simp is_field_merging_possible.
      have [fld Hlook Hrty] : exists2 fld, lookup_field_in_type s t s3 = Some fld &
                                           fld.(return_type).(tname) \in get_possible_types s f.(return_type)
        by admit.
      rewrite Hlook /= Hobj /=; apply_and3P.
      admit.
      admit.
      by apply: H0.

    - admit. (* Labeled *)
    - admit. (* Labeled *)

    - move=> Hmerge t Hin; simp is_field_merging_possible.
      have Hobj := (in_possible_types_is_object Hin).
      case Hspread : is_fragment_spread_possible => //=.
      * admit. (* Contradiction : t is subtype of both, then fragment spread should be possible *)
      * by apply: H.

    - move=> Hmerge t Hin; simp is_field_merging_possible.
      have Hobj := (in_possible_types_is_object Hin).
      have -> /= : is_fragment_spread_possible s s6 t by admit. (* t = ty = s6 *)
        by rewrite Hobj /=; apply: H.

    - move=> /andP [Hsmerge Hmerge] t Hin; simp is_field_merging_possible.
      have Hobj := (in_possible_types_is_object Hin).
      case Hspread : is_fragment_spread_possible => //=.
      * rewrite Hobj /=; apply: H => //=.
        admit. (* s6 spreads in t, then t <: s6 *)
      * by apply: H0.
      
  Admitted.

  Lemma object_spreads_in_itself ty :
    is_object_type s ty ->
    is_fragment_spread_possible s ty ty.
  Proof.
    rewrite /is_fragment_spread_possible => /get_possible_types_objectE -> /=.
    rewrite /seqI /=; case: ifP => //=.
    by case/predU1P; left.
  Qed.
    
  Lemma fragment_applies_then_spreads t ty :
    does_fragment_type_apply s t ty ->
    is_fragment_spread_possible s ty t.
  Proof.
    rewrite /does_fragment_type_apply.
    case: ifP => //=.
    * move=> Hobj /eqP ->.
      by apply: object_spreads_in_itself.
      
    * move=> Hnobj; case: ifP => //=.
    + move=> Hintf Hin; rewrite /is_fragment_spread_possible.
      have Hobj := (in_implementation_is_object Hin).
      rewrite get_possible_types_objectE //=.
      rewrite get_possible_types_interfaceE //= /seqI /=.      
      admit.
  Admitted.

  Lemma fragment_N_applies_then_N_spreads t ty :
    does_fragment_type_apply s t ty = false ->
    is_fragment_spread_possible s ty t = false.
  Admitted.

  Lemma fragment_applies_then_is_obj t ty :
    does_fragment_type_apply s t ty ->
    is_object_type s t.
  Proof.
    rewrite /does_fragment_type_apply.
    case: ifP => /= [Hobj /eqP -> | _] //.
    case: ifP => /= [_ /in_implementation_is_object| _] //.
      by case: ifP => //= move/in_union_is_object.
  Qed.
  
    
  Lemma collect_preserves_equiv φ1 φ2 ty :
    ty ⊢ φ1 ≡ φ2 ->
    forall f fld, 
      lookup_field_in_type s ty f = Some fld ->
      is_field_merging_possible s ty φ1 ->
      is_field_merging_possible s ty φ2 ->
      forall rty,
        rty \in get_possible_types s fld.(return_type) ->
                rty ⊢ merge_selection_sets (find_queries_with_label s f ty φ1) ≡
                    merge_selection_sets (find_queries_with_label s f ty φ2).
  Proof.
    elim=> //=; clear ty φ1 φ2.
    - move=> ty f α φ1 φ2 Heq IH f' fld Hlook Hmerge1 Hmerge2 rty Hin.
      simp find_queries_with_label; case: eqP => //= [Hfeq | Hneq]; simp merge_selection_sets => //=.
      * move: Hmerge1 Hmerge2; rewrite 2!is_field_merging_possible_equation_2.
        case Hscope : is_object_type => /= /andP [Hequiv1 _] /andP [Hequiv2 _];
        rewrite -Hfeq ?merge_simple_fields_is_empty; do ? by constructor.
        by apply: (find_all_q_equiv_to_sf_are_simple Hequiv2).
        by apply: (find_all_q_equiv_to_sf_are_simple Hequiv1).
        by apply (find_all_f_equiv_to_sf_are_simple s ty Hequiv2).
        by apply (find_all_f_equiv_to_sf_are_simple s ty Hequiv1). 

      * move/eqP/negbTE in Hneq; rewrite eq_sym in Hneq.
        rewrite -(find_filter_swap f' f) //.
        rewrite -[X in _ ⊢ _ ≡ merge_selection_sets X](find_filter_swap f' f) //.
        apply: (IH f' fld) => //=.
        move: Hmerge1; rewrite is_field_merging_possible_equation_2.
        by case Hscope : is_object_type => /=; case/andP.
        move: Hmerge2; rewrite is_field_merging_possible_equation_2.
        by case Hscope : is_object_type => /=; case/andP.

    - move=> ty f α β χ fld φ1 φ2 Hlook Heqsub IHsub Heq IH f' fld' Hlook2 Hmerge1 Hmerge2 rty Hin.
      simp find_queries_with_label; case: eqP => //= [Hfeq | Hneq]; simp merge_selection_sets => //=.
      * rewrite -Hfeq in Hlook2 *.
        apply: Heqsub => //=.
        by rewrite Hlook2 in Hlook; case: Hlook => <-.
       
      * move/eqP/negbTE in Hneq; rewrite eq_sym in Hneq.
        rewrite -(find_filter_swap f' f) //.
        rewrite -[X in _ ⊢ _ ≡ merge_selection_sets X](find_filter_swap f' f) //.
        apply: (IH f' fld') => //=.
        move: Hmerge1; rewrite is_field_merging_possible_equation_4 Hlook /=.
          by case Hscope : is_object_type => /=; case/and3P.
        move: Hmerge2; rewrite is_field_merging_possible_equation_4 Hlook /=.
          by case Hscope : is_object_type => /=; case/and3P.

        
    - move=> ty t β φ1 φ2 Hfapplies Heq IH f fld Hlook Hmerge1 Hmerge2.
      simp find_queries_with_label; rewrite Hfapplies /= -find_queries_with_label_cat.
      apply: IH => //=.
      move: Hmerge1; rewrite is_field_merging_possible_equation_6.
      rewrite fragment_applies_then_spreads //=.
      case Hscope : is_object_type => //= /andP [Hmerges _].
      have Hobj := (fragment_applies_then_is_obj ty t Hfapplies).
        by rewrite Hobj in Hscope.
        
    - move=> ty t β φ1 φ2 Hfapplies Heq IH f fld Hlook Hmerge2 Hmerge1.
      simp find_queries_with_label; rewrite Hfapplies /= -find_queries_with_label_cat.
      apply: IH => //=.
      move: Hmerge1; rewrite is_field_merging_possible_equation_6.
      rewrite fragment_applies_then_spreads //=.
      case Hscope : is_object_type => //= /andP [Hmerges _].
      have Hobj := (fragment_applies_then_is_obj ty t Hfapplies).
        by rewrite Hobj in Hscope.
      
    - move=> ty t β φ1 φ2 Hfapplies Heq IH f fld Hlook Hmerge1 Hmerge.
      simp find_queries_with_label; rewrite Hfapplies /=.
      apply: IH => //=.
      move: Hmerge1; rewrite is_field_merging_possible_equation_6.
      by rewrite fragment_N_applies_then_N_spreads //=.
      
    - move=> ty t β φ1 φ2 Hfapplies Heq IH f fld Hlook Hmerge2 Hmerge1.
      simp find_queries_with_label; rewrite Hfapplies /=.
      apply: IH => //=.
      move: Hmerge1; rewrite is_field_merging_possible_equation_6.
      by rewrite fragment_N_applies_then_N_spreads.
  Qed.

    

  
  Lemma collect_preserves_merging ty φ :
    is_field_merging_possible s ty φ ->
    forall f fld,
      lookup_field_in_type s ty f = Some fld ->
      forall rty, rty \in get_possible_types s fld.(return_type) ->
                     is_field_merging_possible s rty (merge_selection_sets (find_queries_with_label s f ty φ)).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ ty => //= [| n IH] φ ty; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ.
    case: q => [f α | | f α β | | t β]; simp query_size => Hleq.

    - move=> Hmerge f' fld Hlook rty Hin.
      simp find_queries_with_label; case: eqP => /= [Heq | Hneq].
      * simp merge_selection_sets => /=.
        rewrite merge_simple_fields_is_empty // -Heq.
        move: Hmerge; rewrite is_field_merging_possible_equation_2.
        case Hscope : is_object_type => //= /andP [Hequiv _].
        by apply: (find_all_q_equiv_to_sf_are_simple Hequiv) => //=.
        by apply: (find_all_f_equiv_to_sf_are_simple s ty Hequiv).

      * move/eqP/negbTE in Hneq; rewrite eq_sym in Hneq.
        rewrite -(find_filter_swap _ f) //.
        move: Hmerge; rewrite is_field_merging_possible_equation_2.
        have Hfleq := (filter_queries_with_label_leq_size f φ). 
        case Hscope : is_object_type => //= /andP [Hequiv Hmerges];
        apply: (IH _ _ _ _ f' fld) => //=; by ssromega.
        

    - admit. (* Labeled *)

    - move=> Hmerge f' fld Hlook rty Hin.
      simp find_queries_with_label; case: eqP => /= [Heq | Hneq].
      * rewrite -Heq in Hlook *.
        simp merge_selection_sets => /=.
        move: Hmerge; rewrite is_field_merging_possible_equation_4 Hlook /=.
        case Hscope : is_object_type => /=; case/and3P => [_ Hsmerge _];
        apply: (is_merging_possible_in_subtype fld.(return_type)) => //=.
        admit.

      * admit.

    - admit. (* Labeled *)

    - move=> Hmerge f fld Hlook rty Hin.
      simp find_queries_with_label.
      case Hfapplies : does_fragment_type_apply => /=.
      * rewrite -find_queries_with_label_cat.
        apply: (IH _ _ _ _ f fld) => //=.
        by rewrite queries_size_cat; ssromega.
        move: Hmerge; rewrite is_field_merging_possible_equation_6.
        rewrite fragment_applies_then_spreads //=.
        case Hscope : is_object_type => //= /andP.
        have Hobj := (fragment_applies_then_is_obj ty t Hfapplies).
        by rewrite Hobj in Hscope.

      * apply: (IH _ _ _ _ f fld) => //=.
          by ssromega.
          move: Hmerge; rewrite is_field_merging_possible_equation_6.
          by rewrite fragment_N_applies_then_N_spreads //=.
  Admitted.

          
        
  (* 
     This property is not valid without some kind of property, meaning that :
          ty ⊢ φ1 ≡ φ2 ->
          ∀ φ, 
             ty ⊢ φ ++ φ1 ≡ φ ++ φ2 
             
             is not always true.

     Example: 
              φ1 := f ; f { β } 
              φ2 := f
              φ := f { χ }
             
             φ1 is equivalent to φ2 in the current definition, but combined with φ
             they are no longer equivalent.
             The thing is that the relation is implicitly exploiting the fact that 
             there won't be two fields with the same label but different structure
             (eg. f and f { β })

     Properties I need :
     1) lookup ≠ ⊥
     2) merge (find f φ1) ≡ merge (find f φ2) : How?
        * equiv is on a subtype of field's return type 
        * find f will find only queries with the same structure (all simple or all nested) 
        * fields found must also lookup to field with same return type (or subtype, etc)
   *)

    
  Theorem equiv_cat ty φ φ' β β' :
    is_field_merging_possible s ty β ->
    is_field_merging_possible s ty β' ->
    ty ⊢ φ ≡ φ' ->
    ty ⊢ β ≡ β' ->
    ty ⊢ φ ++ β ≡ φ' ++ β'.
  Proof.
    move=> Hmerge1 Hmerge2 Heq1 Heq2.
    apply: equiv_trans.
    apply: equiv_cat_hd.
    exact: Heq1.
      by apply: equiv_cat_tail.
  Qed.
  
  
  
 
 

  
  Lemma find_ground_obj_swap ty f φ :
    is_object_type s ty ->
    find_queries_with_label s f ty (ground s ty φ) =
    ground s ty (find_queries_with_label s f ty φ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => //= [| n IH] ty φ.
    - by rewrite leqn0 => /queries_size_0_nil ->.
    - case: φ => //=; case=> [f' α | l f' α | f' α β | l f' α β | t β] φ; simp query_size => Hleq Hscope.

    - simp ground; rewrite Hscope; simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH.
      by simp ground; rewrite Hscope /= IH.
    - simp ground; rewrite Hscope; simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH.
      by simp ground; rewrite Hscope /= IH.

    - simp ground; case Hlook : lookup_field_in_type => [fld|] //=.
      * rewrite Hscope /=; simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH => //=; ssromega.
          by simp ground; rewrite Hlook /= Hscope /= IH //; ssromega.
      * simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH => //=; ssromega.
        by simp ground; rewrite Hlook /=; apply: IH => //=; ssromega.

    - simp ground; case Hlook : lookup_field_in_type => [fld|] //=.
      * rewrite Hscope /=; simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH => //=; ssromega.
          by simp ground; rewrite Hlook /= Hscope /= IH //; ssromega.
      * simp find_queries_with_label; case: eqP => //= Heq; last by apply: IH => //=; ssromega.
        by simp ground; rewrite Hlook /=; apply: IH => //=; ssromega.

    - simp ground; rewrite Hscope /=.
      case Hfapplies: does_fragment_type_apply => //=.
      * simp find_queries_with_label; rewrite Hfapplies /=.
        rewrite ground_cat find_queries_with_label_cat.
        by rewrite !IH //; ssromega.
      * simp find_queries_with_label; rewrite Hfapplies /=; apply: IH => //=; ssromega.
  Qed.




      
    


    



 

  Lemma inline_nested_field_is_equiv α β fld f ty ptys :
    is_object_type s ty ->
    lookup_field_in_type s ty f = Some fld ->
    uniq ptys ->
    ty \in ptys ->
           ty ⊢ [seq InlineFragment t [:: NestedField f α β] | t <- ptys] ≡ [:: NestedField f α β].
  Proof.
    elim: ptys => //= t ptys IH Hscope Hlook /andP [Hnin Huniq].
    rewrite inE => /orP [/eqP Heq | Hin].
    - rewrite -Heq.
      apply: EIF11 => /=.
      * by apply: (object_applies_to_itself ty Hscope).
      * apply: (ENF _ _ _ _ _ fld) => //=.
        move=> rty Hin.
        simp find_queries_with_label.
        have -> : forall φ,
            ty \notin φ ->
            find_queries_with_label s f ty [seq InlineFragment t' [:: NestedField f α β] | t' <- φ] = [::].
        admit.
        apply: equiv_refl.
        admit.
        rewrite filter_frag //=; simp filter_queries_with_label.
        apply: empty_frag_equiv_nil.
          by apply_andP; apply/eqP.

  Admitted.

      
    
  Lemma is_merging_possible_in_hd ty φ1 φ2 :
    is_field_merging_possible s ty (φ1 ++ φ2) ->
    is_field_merging_possible s ty φ1.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n ty φ1 φ2 => //= [| n IH] ty φ1 φ2 ; first by rewrite leqn0 => /queries_size_0_nil ->.

    case: φ1 => //=.
    case=> [f α | l f α | f α β | l f α β | t β] φ1; simp query_size => Hleq.
    - rewrite !is_field_merging_possible_equation_2.
      case is_object_type => /=; rewrite ?find_queries_with_label_cat ?find_fields_cat ?filter_queries_with_label_cat ?all_cat //=.

      * move=> /andP [/andP [Heq _] Hmerge].
        apply_andP.
        apply: IH => //=.
          by have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
          exact: Hmerge.
      
      * move=> /andP [/andP [Heq _] Hmerge].
        apply_andP.
        apply: IH.
          by have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
          exact: Hmerge.


    - admit. (* Labeled *)

    - rewrite !is_field_merging_possible_equation_4.
      case lookup_field_in_type => //= fld.
      case is_object_type => /=; rewrite ?find_queries_with_label_cat ?find_fields_cat ?filter_queries_with_label_cat ?all_cat //=;
      move=> /and3P [/andP [Heq _] Hsmerge Hmerge].
      apply_and3P.
      * have Hbeq : queries_size (β ++ merge_selection_sets (find_queries_with_label s f ty φ1)) <= n.
          rewrite queries_size_cat.
          have Hfleq := (found_queries_leq_size s f ty φ1).
          by have Hmleq := (merged_selections_leq (find_queries_with_label s f ty φ1)); ssromega.
        rewrite merge_selection_sets_cat catA in Hsmerge.
        by have Hm := (IH fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s f ty φ1))
                                        (merge_selection_sets (find_queries_with_label s f ty φ2))
                                        Hbeq
                                        Hsmerge).

      * apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
          exact: Hmerge.

      apply_and3P.
      * have Hbeq : queries_size (β ++ merge_selection_sets (find_fields_with_response_name f φ1)) <= n.
          rewrite queries_size_cat.
          have Hfleq := (found_fields_leq_size f φ1).
          by have Hmleq := (merged_selections_leq (find_fields_with_response_name f φ1)); ssromega.
        rewrite merge_selection_sets_cat catA in Hsmerge.
        by have Hm := (IH fld.(return_type) (β ++ merge_selection_sets (find_fields_with_response_name f φ1))
                                        (merge_selection_sets (find_fields_with_response_name f φ2))
                                        Hbeq
                                        Hsmerge).

      * apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
          exact: Hmerge.

    - admit. (* Labeled *)

    - rewrite 2!is_field_merging_possible_equation_6.
      case is_fragment_spread_possible => //=; last by apply: IH => //=; ssromega.
      case is_object_type => /=.
      * by rewrite catA; apply: IH; rewrite queries_size_cat.
      * rewrite catA; case/andP=> [Hmerge1 Hmerge2].
        apply_andP; apply: IH; rewrite ?queries_size_cat; do ? ssromega.
        exact: Hmerge1.
        exact: Hmerge2.
  Admitted.

  Lemma in_possible_type_share_fields ty :
    forall t,
      t \in get_possible_types s ty ->
            forall f fld,
              lookup_field_in_type s ty f = Some fld ->
              exists2 fld', lookup_field_in_type s t f = Some fld' &
                            is_subtype s fld'.(return_type) fld.(return_type).
  Proof.
  Admitted.
          
  Lemma subtype_possible_typesE t ty :
    is_subtype s t ty ->
    t = ty \/ t.(tname) \in get_possible_types s ty.
  Proof.
    funelim (is_subtype s t ty) => //=.
    - case/or3P=> [/eqP ->]; first by left.
      * move=> Hdecl; right.
        have /get_possible_types_interfaceE -> := (declares_implementation_are_interfaces Hdecl).
        by apply/declares_in_implementation.
      * move=> Hin; right.
        by have /get_possible_types_unionE -> := (in_union Hin).
    - move=> Hsub.
      case: (H Hsub) => [-> | Hin]; [by left | by right].
  Qed.
    
    
  Lemma ground_subtype_equiv t ty φ :
    t \in get_possible_types s ty ->
    is_field_merging_possible s ty φ ->
          t ⊢ ground s ty φ ≡ ground s t φ.
  Proof.
    move=> Hin.
    have Hobj := (in_possible_types_is_object Hin).
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ t Hobj Hin => //= [| n IH] ty φ t Hobj Hin; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //=; case => [f α | l f α | f α β | l f α β | t' β] φ; simp query_size => Hleq Hmerge.

    - simp ground; rewrite Hobj /=.
      case Hscope : is_object_type => //=.
      * apply: ESF => //=.
        rewrite 2!filter_ground_swap; apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        move: Hmerge; rewrite is_field_merging_possible_equation_2 Hscope /=.
          by case/andP.

      * apply: equiv_trans.
        apply: equiv_cat_hd.
        apply: inline_simple_field_is_equiv => //=.
        apply: ESF => //=.
        rewrite 2!filter_ground_swap; apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        move: Hmerge; rewrite is_field_merging_possible_equation_2 Hscope /=.
          by case/andP.

    - admit. (* Labeled *)
      
    - simp ground.
      have [fld1 Hlook1] : exists fld1, lookup_field_in_type s ty f = Some fld1 by admit.
      have [fld2 Hlook2] : exists fld2, lookup_field_in_type s t f = Some fld2 by admit.
      have Hrtyeq : is_subtype s fld2.(return_type) fld1.(return_type) by admit.
      rewrite Hlook1 Hlook2 /= Hobj /=.
      case Hscope : is_object_type => //=.
      + have Hteq := (in_object_possible_types Hscope Hin).
        have Hfeq : fld2 = fld1 by rewrite -Hteq Hlook2 in Hlook1; case: Hlook1.
        rewrite Hfeq.
        apply: (ENF _ _ _ _ _ fld1) => //=; first by rewrite -Hfeq.
        move=> rty Htin.
        rewrite -Hteq.
        apply: equiv_trans.
        apply: equiv_cat_hd.
        apply: IH => //=; do ? ssromega.
        apply: (in_possible_types_is_object Htin).
        move: Hmerge; rewrite is_field_merging_possible_equation_4 Hlook1 /= Hscope /=.
        case/and3P => [_ Hsmerge _].
        apply: is_merging_possible_in_hd => //=.
        exact: Hsmerge.
        apply: equiv_cat_hd.
        apply: equiv_sym.
        apply: IH => //=; do ? ssromega.
        apply: in_possible_types_is_object; exact: Htin.
        move: Hmerge; rewrite is_field_merging_possible_equation_4 Hlook1 /= Hscope /=.
        case/and3P => [_ Hsmerge _].
        apply: is_merging_possible_in_hd => //=.        
        exact: Hsmerge.
        rewrite 2!filter_ground_swap; apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        move: Hmerge; rewrite is_field_merging_possible_equation_4 Hlook1 /= Hscope /=.
          by case/and3P.

      + apply: equiv_trans.
        apply: equiv_cat_hd.
        apply: inline_nested_field_is_equiv => //=.
        exact: Hlook2.
        admit.

        apply: (ENF _ _ _ _ _ fld2) => //=.
        move=> rty Htin.
        apply: equiv_cat.
        admit.
        admit.
        apply: equiv_sym.
        apply: equiv_trans.
        apply: IH => //=.
        apply: (in_possible_types_is_object Htin).
        admit.
        admit.
        apply: equiv_sym; apply: IH => //=.
        admit.
        admit.
        admit.
        admit.
        apply: collect_preserves_equiv => //=.
        apply: IH => //=; admit.
        exact: Hlook2.
        admit. admit. 
        exact: Htin.
        admit.    

    - admit. (* Labeled *)

    - simp ground; rewrite Hobj /=.
      case Hscope : is_object_type => //=.
      * have Hteq := (in_object_possible_types Hscope Hin).
        rewrite Hteq.
          by case Hfapplies1 : does_fragment_type_apply => //=.

      * case Ht : is_object_type => /=.
        + case Hfapplies1 : does_fragment_type_apply => //=; case Hfapplies2 : does_fragment_type_apply => //=.
          apply: EIF11 => //=.
          have Hteq : t' = t.
          by rewrite /does_fragment_type_apply Ht eq_sym in Hfapplies2; apply/eqP.
          move: Hmerge; rewrite is_field_merging_possible_equation_6 Hteq.
          have -> /= : is_fragment_spread_possible s t ty by admit.
          rewrite Hscope /= => /andP [Hmerge1 Hmerge2].
          apply: equiv_cat_tail => //=.
          apply: IH => //=; ssromega.
          admit. (* ground preserves merging *)
          admit. (* ground preserves merging *)
          

          apply: EIF21 => //=.
          apply: IH => //=; do ? ssromega.
          move: Hmerge; rewrite is_field_merging_possible_equation_6.
          have -> /= : is_fragment_spread_possible s t' ty by admit.
          by rewrite Hscope /= => /andP [Hmerge1 Hmerge2].

          have Hteq : t' = t by rewrite /does_fragment_type_apply Ht eq_sym in Hfapplies2; apply/eqP.
          admit. (* Contradiction : t = t' then both apply to ty -><- *)

          apply: IH => //=; do ?ssromega.
          move: Hmerge; simp is_field_merging_possible.
          by have -> /= : is_fragment_spread_possible s t' ty = false by admit.

          
        + case Hfapplies : does_fragment_type_apply => /=.
          apply: equiv_trans.
          apply: (equiv_cat_hd _ _ [:: InlineFragment t (ground s t β)]).
          admit.
          apply: EIF11 => //=.
          by apply: object_applies_to_itself; apply: (in_possible_types_is_object Hin). 
          admit.
          
          admit. (* map is equiv to ground s t φ *)
          
          
          
  Admitted.


 


     

  Lemma ground_preserves_merging ty φ :
    is_field_merging_possible s ty φ ->
    is_field_merging_possible s ty (ground s ty φ).
  Proof.
    funelim (is_field_merging_possible s ty φ) => //=.

    - move=> /andP [Hequiv Hmerge].
      simp ground; rewrite Heq /=; simp is_field_merging_possible; rewrite Heq /=.
      apply_andP.
      admit.
      by rewrite filter_ground_swap; apply: H.

    - move=> /andP [Hequiv Hmerge].
      simp ground; rewrite Heq /=; simp is_field_merging_possible.

  Abort.
      
 
    
  Lemma filter_reground_swap f ty φ :
    filter_queries_with_label f (reground s ty φ) = reground s ty (filter_queries_with_label f φ).
  Admitted.


    
        
  (*
    I don't really need equiv cat here... But I still need some properties of the queries.
    In particular, I would like to do the following :
    
    merge (ground ty φ) = ground fld.rty (merge φ)

    - forall q ∈ φ, q.qname = name -> lookup name = Some fld 
   *)
  Lemma ground_equiv1 t φ1 φ2 :
    t ⊢ φ1 ≡ φ2 ->
    forall ty, 
      t \in get_possible_types s ty ->
            is_field_merging_possible s ty φ1 ->
            is_field_merging_possible s ty φ2 ->
            t ⊢ ground s ty φ1 ≡ φ2.
  Proof.    
    elim=> //=; clear t φ1 φ2.

    - move=> t f α φ1 φ2 Hfiltereq IH ty Hin Hmerge1 Hmerge2; simp ground.
      have Hobj := (in_possible_types_is_object Hin).
      case Hscope : is_object_type => //=.
      * apply: ESF; rewrite filter_ground_swap; apply: IH => //=.
        by move: Hmerge1; simp is_field_merging_possible; rewrite Hscope /=; case/andP.
        by move: Hmerge2; simp is_field_merging_possible; rewrite Hscope /=; case/andP.
        
      * apply: equiv_trans.
          by apply: equiv_cat_hd; apply: inline_simple_field_is_equiv.
        apply: ESF. rewrite filter_ground_swap; apply: IH => //=.
        by move: Hmerge1; simp is_field_merging_possible; rewrite Hscope /=; case/andP.
        by move: Hmerge2; simp is_field_merging_possible; rewrite Hscope /=; case/andP.
      

    - move=> t f α β χ fld φ1 φ2 Hlook Hsubequiv IHsub Hfiltereq IH ty Hin Hmerge1 Hmerge2.
      have Hobj := (in_possible_types_is_object Hin).
      simp ground.
      have [fld' Hlook2] : exists fld', lookup_field_in_type s ty f = Some fld' by admit.
      rewrite Hlook2 /=.
      case Hscope : is_object_type => //=.
      * have Hteq := (in_object_possible_types Hscope Hin).
        have -> : fld' = fld by admit.
        apply: (ENF _ _ _ _ _ fld) => //=.
        move=> rty Hrtyin.
        rewrite -Hteq in Hmerge1 Hmerge2 *.                           
        rewrite find_ground_obj_swap //.
        have -> : merge_selection_sets (ground s t (find_queries_with_label s f t φ1)) =
                 ground s fld.(return_type) (merge_selection_sets (find_queries_with_label s f t φ1)).
        admit.

        rewrite -ground_cat.
        apply: IHsub => //=.
        by move: Hmerge1; simp is_field_merging_possible; rewrite Hlook /= Hteq Hscope /=; case/and3P.
        by move: Hmerge2; simp is_field_merging_possible; rewrite Hlook /= Hteq Hscope /=; case/and3P.

        rewrite filter_ground_swap; apply: IH => //=.
        by move: Hmerge1; simp is_field_merging_possible; rewrite Hlook2 /= Hscope /=; case/and3P.
        by move: Hmerge2; simp is_field_merging_possible; rewrite Hlook2 /= Hscope /=; case/and3P.

        
      * apply: equiv_trans.
        apply: equiv_cat_hd.
        apply: inline_nested_field_is_equiv => //=.
        exact: Hlook.
        admit.
        move: Hmerge1; simp is_field_merging_possible; rewrite Hlook2 /= Hscope /=.
        move=> /and3P [Hequiv Hsmerge Hmerge].
        apply: (ENF _ _ _ _ _ fld) => //=.
        move=> rty Hrtyin.
        admit.

        admit.
        
      
    - intros; simp ground.
      have Hobj := (in_possible_types_is_object H2).
      case Hscope : is_object_type => //=.
      * have Hteq := (in_object_possible_types Hscope H2).
        rewrite -Hteq H /=.
        move: H3; rewrite is_field_merging_possible_equation_6.
        have -> /= : is_fragment_spread_possible s t ty0 by admit.
        rewrite Hscope /= => Hmerge.
        rewrite -ground_cat; apply: H1 => //=.
          by rewrite {2}Hteq.
          by rewrite Hteq.
          by rewrite Hteq.  
          
      * case Ht : is_object_type => /=.
        have Hteq : t = ty by rewrite /does_fragment_type_apply Ht eq_sym in H; apply/eqP.
        rewrite Hteq.
        have -> /= : does_fragment_type_apply s ty ty0 by admit.
        apply: EIF11 => //=.
          by apply: object_applies_to_itself.

        apply: equiv_trans.
        apply: equiv_cat_tail.
        apply: (ground_subtype_equiv ty ty0) => //=.
        move: H3; rewrite is_field_merging_possible_equation_6.
        have -> /= : is_fragment_spread_possible s t ty0 by admit.
        by rewrite Hscope /= => /andP [Hmerge Hm].
        apply: is_merging_possible_in_subtype.
        admit.
        exact: H2.
        admit.
        rewrite -ground_cat; apply: H1 => //=.
        admit.
        admit.
        apply: is_merging_possible_in_subtype.
        exact: H4.
        admit.
        
    - intros; apply: EIF12 => //=; apply: H1 => //=.
      admit.
      
    - intros.
      
   
          
          
          
      
  (*
    Missing lemmas : 
    1. Conformance is preserved:
      - filter preserves conformance : wf φ -> wf (filter φ)
      - Subqueries from selections with same response name are still in conformance
      - Inline fragment subqueries conform with rest of list
      - tail conforms when cons conforms

    2. Other :
      [x] Inlining simple fields is equiv to the single field 
      - Inlining nested fields is equiv to the single nested field
      [/] looking up field in supertype exists bc query conforms to it
      [x] find (ground ty φ) = ground ty (find φ) in object scope
      - merge (ground ty φ) = ground fld.rty (merge φ)
      * ty ⊢ ground s ty β ++ ground s sty φ ≡ φ'
      - Prove inlines on intersection of types is equiv to one single fragment 
      - Prove that if t ∈ subtypes (ty) ∧ t ∈ subtypes (ty') -> t ∈ subtypes (ty) ∩ subtypes (ty')

   *)
  Lemma ground_equiv1 t φ1 φ2 :
    t ⊢ φ1 ≡ φ2 ->
    forall ty, 
      t \in get_possible_types s ty ->
            queries_conform s ty φ1 ->
            queries_conform s ty φ2 ->
            t ⊢ ground s ty φ1 ≡ φ2.
  Proof.        
    elim=> //=.

    - intros; simp ground.
      case Hscope : is_object_type => /=.
      * apply: ESF.
        rewrite filter_ground_swap; apply: H0 => //=; admit. (* filter preserves conformance *)

      * apply: equiv_trans.
        apply: equiv_cat_hd.
        apply: (inline_simple_field_is_equiv _ ty f α (in_possible_types_is_object H1)) => //=.
        apply: ESF; rewrite filter_ground_swap; apply: H0 => //=; admit. (* filter preserves conformance *)
        
        
    - intros; simp ground.
      case Hlook2 : lookup_field_in_type => [fld'|] //=; last by admit.
      case Hscope : is_object_type => /=.

      * have Hteq : ty = ty0 by apply (in_object_possible_types Hscope H4).
        rewrite -Hteq H in Hlook2; case: Hlook2 => <-.
        apply: (ENF _ _ _ _ _ fld) => //=.
        + move=> t' Htin.
          rewrite -Hteq.
          rewrite (find_ground_obj_swap ty _ _ (in_possible_types_is_object H4)) //=.
          have -> : merge_selection_sets (ground s ty (find_queries_with_label s f ty φ)) = 
                   ground s fld.(return_type) (merge_selection_sets (find_queries_with_label s f ty φ)).
          by admit.

        rewrite -ground_cat.
        apply: H1 => //=; admit. (* Subqueries conform *)

        
        rewrite filter_ground_swap; apply: H3 => //=; admit. (* filter preserves conformance *)

        
      * have Htrans : forall ptys,
          (* uniq ptys -> *)
          ty \in ptys ->
                 ty ⊢ [seq InlineFragment t' [:: NestedField f α (ground s fld.(return_type) β)] | t' <- ptys] ≡
                    [:: NestedField f α (ground s fld.(return_type) β)].
          by admit.

        have Hrty : fld'.(return_type) = fld.(return_type) by admit.
        rewrite Hrty.
        apply: equiv_trans.
        apply: equiv_cat_hd; exact: (Htrans (get_possible_types s ty0)).
        apply: (ENF _ _ _ _ _ fld) => //=.
        move=> t' Htin.
        have -> : find_queries_with_label s f ty (ground s ty0 φ) = ground s ty (find_queries_with_label s f ty φ).
          by admit.
        have -> : merge_selection_sets (ground s ty (find_queries_with_label s f ty φ)) = 
                 ground s fld.(return_type) (merge_selection_sets (find_queries_with_label s f ty φ)).
          by admit.

        rewrite -ground_cat; apply: H1 => //=; admit. (* Subqueries conform *)

        rewrite filter_ground_swap; apply: H3 => //=; admit. (* filter preserves conformance *)

        

    - intros; simp ground.
      case Hscope : is_object_type => /=.
      (* ty0 ∈ Ot *)
      * have Hteq : ty0 = ty by admit.
        rewrite Hteq H /= -ground_cat; apply: H1 => //=.
          by rewrite -{2}Hteq.
          admit. (* Queries conform *)
            by rewrite -Hteq.

      (* ty0 ∈ At *)
      * case Ht : is_object_type => /=.
        have Hteq : t0 = ty by admit. (* Same object *)
        have -> /= : does_fragment_type_apply s t0 ty0 by admit. (* By subtyping *)
        apply: EIF11 => //=.
        admit. (* Not sure how to solve... Could prove that ground s ty0 ≡ ground s ty or
                  maybe with induction over length ? *)

        have Htrans :
          forall ptys,
            (* uniq ptys -> *)
            ty \in ptys ->
                   ty ⊢ [seq InlineFragment sty (ground s sty β) | sty <- ptys] ≡ [:: InlineFragment ty (ground s ty β)].
        admit.

        apply: equiv_trans.
        apply: (equiv_cat_hd _ _ [:: InlineFragment ty (ground s ty β)]).
        admit.
        apply: EIF11.
          by apply: (object_applies_to_itself ty (in_possible_types_is_object H2)).
        admit. (* Not sure how to solve... Could prove that ground s ty0 ≡ ground s ty or
                  maybe with induction over length ? *)

    - intros; apply: EIF12 => //=.
      apply: H1 => //=.
      admit. (* Queries conform *)

    - intros; simp ground; case Hscope : is_object_type => //=.
      * have Hteq : ty0 = ty by admit.
        rewrite Hteq H /=.
        apply: H1 => //=.
          by rewrite -{2}Hteq.
          admit. (* Queries conform *)
            by rewrite -Hteq.
 
      * case Ht : is_object_type => /=.
        case Hfapplies : does_fragment_type_apply => /=.
        apply: EIF21 => //=.
        apply: H1 => //=.
        admit. (* Queries conform *)
        apply: H1 => //=.
        admit. (* Queries conform *)

        have Htrans : forall ptys,
            ty \notin ptys ->
            ty ⊢ [seq InlineFragment sty (ground s sty β) | sty <- ptys] ≡ [::].
        admit.

        apply: equiv_trans.
        apply: (equiv_cat_hd _ _ [::]).
        admit.
        rewrite cat0s; apply: H1 => //=.
        admit.

    - intros; apply: EIF22 => //=.
      apply: H1 => //=.
      admit. (* Queries conform *)
  Admitted.


  
    
  Lemma remove_red_equiv t φ1 φ2 :
    t ⊢ φ1 ≡ φ2 ->
    forall ty,
      t \in get_possible_types s ty ->
            are_grounded2 s ty φ1 ->
            are_grounded2 s ty φ2 ->
            t ⊢ remove_redundancies φ1 ≡ φ2.
  Proof.
    elim=> //.

    - intros; simp remove_redundancies.
      apply: ESF.
      rewrite filter_remove_swap filter_filter_absorb //.
      apply: (H0 ty0) => //=; admit. (* filte preserves grounding *)
      
    - intros; simp remove_redundancies.
      apply: (ENF _ _ _ _ _ fld) => //=.
      * move=> t' Htin.
        have -> : find_queries_with_label s f ty (remove_redundancies (filter_queries_with_label f φ)) = [::] by admit.
        simp merge_selection_sets => /=.
        rewrite cats0.
        have -> : find_fields_with_response_name f φ = find_queries_with_label s f ty φ by admit.
        apply: H1 => //=.
        exact: Htin.
        admit. (* subqueries are grounded wrt return type *)
        admit.
        
      * rewrite filter_remove_swap filter_filter_absorb //; apply: H3 => //=.
        exact: H4.
        admit.
        admit.

    - intros; simp remove_redundancies.
      apply: EIF11 => //=.

  Abort.
        
  Lemma remove_red_equiv ty φ :
    are_grounded2 s ty φ ->
    forall t, t \in get_possible_types s ty ->
               t ⊢ remove_redundancies φ ≡ φ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => //= [| n IH] ty φ; first by rewrite leqn0 => /queries_size_0_nil ->; simp remove_redundancies; constructor.

    case: φ => //; case=> [f α | | f α β | | t' β] φ; simp query_size => Hleq Hg t Hin.

    - simp remove_redundancies; case Hlook : (lookup_field_in_type s ty f) => [fld|] /=.
      * constructor.
        rewrite filter_remove_swap filter_filter_absorb //.
        apply: (IH ty) => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        apply: filter_preserves_grounded2.
          by have Hgs := (are_grounded2_consE Name Vals s ty _ φ Hg).
          
      * apply: ESF.
        rewrite filter_remove_swap filter_filter_absorb //.
        apply: (IH ty) => //=.
          by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        apply: filter_preserves_grounded2.
          by have Hgs := (are_grounded2_consE Name Vals s ty _ φ Hg).
          
        
    - admit. (* Labeled *)

    - simp remove_redundancies; case Hlook : (lookup_field_in_type s t f) => [fld|] /=.
      
      * apply: ENF => //=; first exact: Hlook.
        + move=> t' Htin.
          rewrite -filter_remove_swap.
          have -> : find_queries_with_label s f t (filter_queries_with_label f (remove_redundancies φ)) = [::] by admit.
          simp merge_selection_sets => /=.
          rewrite cats0.
          have -> : find_fields_with_response_name f φ = find_queries_with_label s f t φ by admit.
          (* If queries are grounded with field then ty ∈ Ot, which means all in φ are fields *)
          apply: (IH fld.(return_type)) => //=.
          admit. (* Size ≤ n *)

          admit. (* Subqueries are grounded *)
          
        + rewrite filter_remove_swap filter_filter_absorb //.
          apply: (IH ty) => //=.
            by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
          apply: filter_preserves_grounded2.
            by have Hgs := (are_grounded2_consE Name Vals s ty _ φ Hg).
            
      * admit. (* Contradiction if field in subtype but not supertype *)  

    - admit. (* Labeled *)
      
    - case Hfapplies : (does_fragment_type_apply s t t'); simp remove_redundancies.

      * apply: EIF11 => //=.
        apply: EIF12 => //=.
        have Hteq : t' = t by admit. (* t', t ∈ Ot ∧ frag applies → both are the same *)
        rewrite Hteq.
        apply: equiv_trans.
        apply: (equiv_cat t _ _ _ [::]).
        apply: (IH ty) => //=.
        admit. (* leq size *)
        admit. (* grounded *)

        admit. (* all are inlines, but none matches t -> none is evaluated *)

        rewrite cats0.
        apply: equiv_cat_tail.
        admit. (* Similar to before, only those fragments with guard = t are evaluated *)


      * apply: EIF21 => //=.
        apply: EIF22 => //=.
        apply: equiv_trans.
        apply: (IH ty) => //=.
        admit. (* leq size *)
        admit. (* grounding is preserved *)
        admit. (* Filtering fragments that don't apply is the same *)
  Admitted.
        
        
  Theorem ground_equiv ty φ :
    forall t, t \in get_possible_types s ty ->
               t ⊢ ground s ty φ ≡ φ.
  Proof.
      by intros; apply: ground_equiv1.
  Qed.


  Theorem equiv_eval ty φ1 φ2 :
    forall t, t \in get_possible_types s ty ->
               t ⊢ φ1 ≡ φ2 ->
               forall u, u.(type) = t ->
                    ⟦ φ1 ⟧ˢ in u = ⟦ φ2 ⟧ˢ in u.
  Proof.
    move=> t Hin.
    elim=> //=.
    
    - intros; simp execute_selection_set.
      case Hlook: lookup_field_in_type => //= [fld |].

      * by case (u.(fields) _) => [[v | vs] |] //=; congr cons; apply: H0.

      * admit. (* lookup null *)

    - intros; simp execute_selection_set.
      rewrite H4 H /=.
      case fld.(return_type) => /= rty.
      * case Hoh: ohead => [v |] /=; congr cons; last by apply: H3.
        rewrite H4.
        rewrite (H1 v.(type)) //=.
        admit. (* neighbour's type <: fld's return type *)
        by apply: H3.

      * congr cons; last by apply: H3.
        congr pair; congr Array; apply/eq_in_map=> v Hvin; congr Object.
        rewrite H4 (H1 v.(type)) //=.
        admit. (* neighbour's type <: fld's return type *)

    all: do ?[ intros; simp execute_selection_set;
                 by rewrite H2 H /=; apply: H1].

  Admitted.



  Theorem normalize_preserves_semantics ty u φ :
    u.(type) \in get_possible_types s ty ->
                 ⟦ normalize s ty φ ⟧ˢ in u = ⟦ φ ⟧ˢ in u.
  Proof.
    move=> Hin.
    rewrite /normalize.
    have Hrem : ⟦ remove_redundancies (ground s ty φ) ⟧ˢ in u = ⟦ ground s ty φ ⟧ˢ in u.
    apply: equiv_eval => //=.
    exact: Hin.
    apply: remove_red_equiv => //=.
    apply: ground_are_grounded2 => //=.
    exact: Hin.
    have Hg : ⟦ ground s ty φ ⟧ˢ in u = ⟦ φ ⟧ˢ in u.
    apply: equiv_eval => //=.
    exact: Hin.
    apply: ground_equiv.
    exact: Hin.
    by rewrite Hrem Hg.
  Qed.

      
        
        


  Lemma repeated_eval_same u q1 qs :
    
    ⟦ q1 :: q1 :: qs 
  Lemma sf_preserves u qs1 qs2 :
    BaseRewrite u.(type) qs1 qs2 ->
    ⟦ qs1 ⟧ˢ in u = ⟦ qs2 ⟧ˢ in u.
  Proof.
    elim.
    - move=> f α qs; simp execute_selection_set; case Hlook : lookup_field_in_type => [fld|] //=.
      case (u.(fields) _) => [[v | vs] |] //=; congr cons.
      all: do ? [by rewrite filter_queries_with_label_cat; simp filter_queries_with_label => /=; case: eqP => //= _;
                                                                                                            simp filter_queries_with_label; rewrite cats0].
      * admit. (* lookup = null *)

    - move=> f α φ β qs Hfind; simp execute_selection_set; case Hlook : lookup_field_in_type => [fld|] //=.
      case fld.(return_type) => rty /=.
      * case ohead => [v |] /=; rewrite filter_queries_with_label_cat; simp filter_queries_with_label => /=.
        rewrite find_queries_with_label_cat Hfind /=.
        simp merge_selection_sets; rewrite cats0.
        simp filter_queries_with_label.
        rewrite /find_queries_with_label.
        simp ble; case: eqP => //= _; simp ble; simp filter_queries_with_label.
        by simp merge_selection_sets => /=; rewrite !cats0.

        by case: eqP => //= _; simp filter_queries_with_label; rewrite cats0.

      * congr cons.
        congr pair; congr Array; apply/eq_in_map => v Hin.
        rewrite find_queries_with_label_cat Hfind /=; simp merge_selection_sets; rewrite cats0.
        rewrite /find_queries_with_label; simp ble; case: eqP => //= _.
        by simp merge_selection_sets => /=; rewrite cats0.
        rewrite filter_queries_with_label_cat; simp filter_queries_with_label => /=; case: eqP => //= _.
        by simp filter_queries_with_label; rewrite cats0.
         
      * admit. (* lookup = null *)

    - move=> φ1 φ; simp execute_selection_set; case Hfapplies : does_fragment_type_apply => /=.
      rewrite cats0.
      admit.
        by simp execute_selection_set; rewrite Hfapplies /=.

    - simp execute_selection_set; case Hfapplies : does_fragment_type_apply => //=.
        by rewrite cats0.
        admit. (* Contradiction - needs info on node *)

    - simp execute_selection_set; case Hfapplies : does_fragment_type_apply => //=.
      by simp execute_selection_set; rewrite Hfapplies.
      
  Admitted.
  

 Reserved Notation "⦃ queries 'in' u ⦄" (at level 50).
  
   Equations? execute_selection_set2 u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];

      execute_selection_set2 u (SingleField f α :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _ 
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (f, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
            | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
            | None => (f, Leaf Null) :: ⦃ qs in u ⦄
            };
        | _ := ⦃ qs in u ⦄ (* Error *)
        };
      
      execute_selection_set2 u (LabeledField l f α :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some _ 
            with u.(fields) (Field f α) :=
            {
            | Some (inl value) => (l, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
            | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
            | None => (l, Leaf Null) : ⦃ qs in u ⦄
            };
        | _ := ⦃ qs in u ⦄ (* Error *)
        };

      
      execute_selection_set2 u (NestedField f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (f, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
            | NT ty
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (f, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
                
                | _ =>  (f, Leaf Null) :: ⦃ qs in u ⦄
                }
            };

        | None => ⦃ qs in u ⦄ (* Error *)
        };
    execute_selection_set2 u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some fld
            with fld.(return_type) :=
            {
            | ListType _ => (l, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
            | NT ty
                with ohead (neighbours_with_field g u (Field f α)) :=
                {
                | Some v => (l, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
                
                | _ =>  (l, Leaf Null) :: ⦃ qs in u ⦄
                }
            };

        | None => ⦃ qs in u ⦄ (* Error *)
        };

       
        execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⦃ φ ++ qs in u ⦄;
        | _ := ⦃ qs in u ⦄
        }

    }
   where "⦃ queries 'in' u ⦄" := (execute_selection_set2 u queries).
   all: do [simp query_size]; do ?by ssromega.
     by rewrite queries_size_cat; ssromega.
  Qed.



   Lemma execute_selection_set2_cat u qs1 qs2 :
    ⦃ qs1 ++ qs2 in u ⦄ = ⦃ qs1 in u ⦄ ++ ⦃ qs2 in u ⦄.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size qs1)) => n.
    elim: n qs1 => // [| n IH] qs1.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: qs1 => //=; case=> [f α | l f α | f α φ | l f α φ | t φ] qs; simp query_size => Hleq; simp execute_selection_set2.
      * Admitted.

  
  Lemma all_invalid_fragments_eval u φ qs :
    all (fun q => q.(is_inline_fragment)) qs ->
    are_grounded s qs ->
    all (fun q => ~~are_similar q (InlineFragment u.(type) φ)) qs ->
    ⦃ qs in u ⦄ = [::].
  Proof.
    elim: qs => //=; case=> // t χ qs IH /andP [Hinl Hinls].
    simp are_grounded; simp is_field.
  Admitted.

   Theorem execs_on_nrgtnf_are_equivalent u φ :
    are_grounded s φ ->
    are_non_redundant φ ->
    ⦃ φ in u ⦄ = ⟦ φ ⟧ˢ in u.
   Proof.
   Admitted.
   (*
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => [| n IH] φ u.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: φ => //=; case=> /= [f α | l f α | f α φ | l f α φ | t φ] qs Hleq.
      * simp are_grounded; simp is_field => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (SingleField f α)) // IH //; by apply: asdf.
      
      * simp are_in_normal_form => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (LabeledField l f α)) // IH //; by apply: asdf.

        
      * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
          by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
          by rewrite IH //; ssromega.
          
        + rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //. 
          congr cons; last by apply: IH => //; ssromega.
          congr pair; congr Array.
          apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
        + by rewrite IH //; ssromega.
             
      * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
          by rewrite IH //; ssromega.
         
        + rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. 
          congr cons; last by apply: IH => //; ssromega.
          congr pair; congr Array.
          apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
        + by rewrite IH //; ssromega.

       
      * simp are_in_normal_form => /and5P [Hobj Hflds Hnf Hinl Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].
        simp execute_selection_set; simp execute_selection_set2.
        case Hfrag: does_fragment_type_apply => //=; last by apply: IH => //; ssromega.
        rewrite execute_selection_set2_cat.
        rewrite (all_invalid_fragments_eval u φ qs) // ?cats0; last first.
        rewrite /does_fragment_type_apply Hobj in Hfrag.
          by move/eqP in Hfrag; rewrite Hfrag.        
        
          
        rewrite all_invalid_fragments_exec //; [apply: IH => //; rewrite -/(queries_size φ) in Hleq; ssromega|].
        rewrite /does_fragment_type_apply Hobj in Hfrag.
          by move/eqP in Hfrag; rewrite Hfrag.
  Qed.

    *)

       
  Lemma sf_evalE f α u qs :
    [\/ exists value, ⟦ SingleField f α :: qs ⟧ˢ in u = (f, Leaf (SingleValue value)) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u,
       exists values, ⟦ SingleField f α :: qs ⟧ˢ in u = (f, Array (map (Leaf \o SingleValue) values)) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u,
       ⟦ SingleField f α :: qs ⟧ˢ in u = (f, Leaf Null) :: ⟦ filter_queries_with_label f qs ⟧ˢ in u |
     ⟦ SingleField f α :: qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u].
  Proof.
    simp execute_selection_set; case lookup_field_in_type => /= [fld|]; last by constructor 4.
    by case (u.(fields) _) => [[v | vs]|]; [constructor 1; exists v | constructor 2; exists vs | constructor 3].
  Qed.
  
 


 

  Lemma filtering_invalid_fragments_preserves_semantics t u qs :
    are_grounded_inlines s qs -> 
    does_fragment_type_apply s u.(type) t = false -> 
    ⟦ filter_fragments_with_guard t qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
    elim: n qs u t => /= [| n IH] qs u t.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: qs => //=; case=> // t' φ qs; simp query_size => Hleq; simp is_grounded => /and3P [_ /andP [Htobj Hginls] Hgflds] Hfapplies.
      simp filter_fragments_with_guard; case: eqP => //= [-> | Hneq]; simp execute_selection_set.
      * by rewrite Hfapplies /=; apply: IH => //; ssromega.
      * case: does_fragment_type_apply => //=; last by apply: IH => //; ssromega.
        (* by apply: qwe; apply: IH => //; ssromega. *)
  Admitted.

                                 

  Lemma eval_filter k qs1 qs2 u :
    ⟦ qs1 ⟧ˢ in u = ⟦ qs2 ⟧ˢ in u ->
    ⟦ filter_queries_with_label k qs1 ⟧ˢ in u = ⟦ filter_queries_with_label k qs2 ⟧ˢ in u.
  Proof. 
    move: {2}(queries_size _) (leqnn (queries_size qs1)) => n.
    elim: n qs1 qs2 u => /= [| n IH] qs1 qs2 u.
    - rewrite leqn0 =>  /queries_size_0_nil ->; simp execute_selection_set. admit.
  Admitted.
  
  Lemma eval1 qs qs1 qs2 u :
    ⟦ qs1 ⟧ˢ in u = ⟦ qs2 ⟧ˢ in u ->
    ⟦ qs ++ qs1 ⟧ˢ in u = ⟦ qs ++ qs2 ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
    elim: n qs qs1 qs2 u => /= [| n IH] qs qs1 qs2 u.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: qs => //; case=> [f α | l f α | f α φ | l f α φ | t φ] qs; simp query_size => Hleq Heq; rewrite 2!cat_cons.

      * simp execute_selection_set; case lookup_field_in_type => [fld|] /=; last by apply: IH.
        case (u.(fields) _) => [[v | vs] |] /=; congr cons; apply: eval_filter; apply: (IH qs qs1) => //=.
                                (* filtering two equivalent queries preserves semantics *)
        
      * simp execute_selection_set; case lookup_field_in_type => [fld|] /=; last by apply: IH.
        case (u.(fields) _) => [[v | vs] |] /=; congr cons;
                                admit. (* filtering two equivalent queries preserves semantics *)
        
      * simp execute_selection_set; case lookup_field_in_type => [fld|] /=; last by apply: IH => //; ssromega.
        case fld.(return_type) => /= rty.
        + case ohead => [v |] /=.
          congr cons.
          congr pair; congr Object.
          apply: (IH φ (merge_selection_sets (find_queries_with_label s f v.(type) (qs ++ qs1)))); first by ssromega.
          admit. (* eval subqueries from similar fields is equiv *)
          admit. (* filtering two equivalent queries preserves semantics *)
          admit. (* filtering two equivalent queries preserves semantics *)

        + congr cons.
          congr pair; congr Array; apply/eq_in_map=> v Hin; congr Object.
          apply: (IH φ (merge_selection_sets (find_queries_with_label s f v.(type) (qs ++ qs1)))); first by ssromega.
          admit. (* eval subqueries from similar fields is equiv *)
          admit. (* filtering two equivalent queries preserves semantics *)


      * admit. (* Copy & Paste *) 
       
      * simp execute_selection_set; case does_fragment_type_apply => /=.
        rewrite 2!catA; apply: IH => //; rewrite queries_size_cat; ssromega.
        by apply: IH => //; ssromega.
  Admitted.
  
  
  Theorem rem_red_ground_sem ty u qs :
    are_grounded2 s ty qs ->
    ⟦ remove_redundancies qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    move=> Hg.
    rewrite -execs_on_nrgtnf_are_equivalent; [
    | admit
    | by apply: remove_redundancies_is_non_redundant].

    funelim (remove_redundancies qs) => //=.
    - simp execute_selection_set2; simp execute_selection_set.
      case Hlook : lookup_field_in_type => [fld|] /=.
      * case (u.(fields) _) => [[v | vs] |] /=; rewrite (H ty) //; admit. (* Filter preserves grounding *)
      * admit. (* lookup = null *)

    - admit. (* Copy & Paste *)

    - simp execute_selection_set2; simp execute_selection_set.
      case Hlook : lookup_field_in_type => [fld|] /=; last admit. (* lookup = null *)
      case fld.(return_type) => rty /=.
      * case ohead => [v |] /=.
        rewrite (H rty) /=.
        rewrite (H0 ty).
        rewrite !find_queries_or_fields_is_same_if_all_fields //.
        admit. (* all are fields *)
        admit. (* Filter preserves grounding *)
        admit. (* subqueries are grounded wtr field's type *)

        rewrite (H0 ty) //; admit. (* Filter preserves grounding *)

      * congr cons.
        congr pair; congr Array; apply/eq_in_map=> v Hin; congr Object.
        rewrite !find_queries_or_fields_is_same_if_all_fields.
        rewrite (H rty) //.
        admit. (* Subqueries are grounded *)
        admit. (* All are fields *)
        apply: (H0 ty); admit. (* Filter preserves grounding *)

    - admit. (* Copy & Paste *)

    - simp execute_selection_set2; simp execute_selection_set.
      case Hfapplies : does_fragment_type_apply => //=.
      rewrite execute_selection_set2_cat.
      rewrite (H s6).
      rewrite (H0 ty).
  Admitted.
      
        

  Lemma adfasqw f α ty qs u :
    is_object_type s ty = false ->
    get_possible_types s ty != [::] ->
    ⦃ remove_redundancies ([seq InlineFragment ty0 [:: SingleField f α] | ty0 <- get_possible_types s ty] ++ ground s ty qs) in u ⦄ =
    ⦃ [seq InlineFragment ty0 (SingleField f α :: merge_selection_sets (find_fragments_with_guard ty0 (ground s ty qs))) | ty0 <- get_possible_types s ty] in u⦄ .
  Proof.
    move=> Hscope Hptys.
    
    
  Abort.
    
    
   Theorem normalize_preserves_semantics ty u qs :
     ⟦ normalize s ty qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
   Proof.
     have [Hg Hnr] := (normalized_queries_are_in_normal_form Name Vals s ty qs).
     rewrite -execs_on_nrgtnf_are_equivalent //.
     rewrite /normalize /=.     
     move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
     elim: n qs ty Hg Hnr u => [| n IH] qs ty Hg Hnr u.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: qs Hg Hnr => //=; case=> [f α | l f α | f α φ | l f α φ | t φ] qs Hg Hnr; simp query_size => Hleq;
      simp ground.
     
    - case Hscope : is_object_type => /=.
      
      simp remove_redundancies; simp execute_selection_set2; simp execute_selection_set.
      case Hlook : lookup_field_in_type => [fld|] /=.
      case (u.(fields) _) => [[v | vs] |] /=; rewrite filter_ground_swap IH //.
      all: do ? by have [Hg' _] := (normalized_queries_are_in_normal_form Name Vals s ty (filter_queries_with_label f qs)).
      all: do ? by have [_ Hnr'] := (normalized_queries_are_in_normal_form Name Vals s ty (filter_queries_with_label f qs)).
      all: do ? by have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.
      admit. (* lookup = ⊥ -> qs should evaluate to the same *)

    - simp try_inline_query; case: eqP => //= Hpty.
      * admit. (* Same as previous *)
      * admit. (* Inlining field *)

    - admit. (* Copy & Paste *)

    - case Hlook1 : lookup_field_in_type => [fld |] /=.
      case Hscope : is_object_type => /=.
      simp remove_redundancies; simp execute_selection_set2.
      simp execute_selection_set.
      case Hlook2 : lookup_field_in_type => [fld2 |] /=.
      case fld2.(return_type) => rty /=.
      case ohead => [v |] /=; congr cons.
      congr pair; congr Object.
      admit.
   Abort.
     
  


        
        

  Lemma exec_filtered_queries_asdf u qs l :
    all (fun kq => kq.1 != l) (⟦ filter_queries_with_label l qs ⟧ˢ in u).
  Proof.
    funelim (filter_queries_with_label l qs) => //=; simp execute_selection_set.
    - 
  Admitted.

 
  Lemma exec_responses_are_non_redundant u qs :
    Response.are_non_redundant (execute_selection_set u qs).
  Proof.
    apply_funelim (execute_selection_set u qs) => //=; clear u qs => u.

    all: do ? by intros; apply_and3P; apply: exec_filtered_queries_asdf.

    all: do ? intros; simp is_non_redundant; apply_and3P;
      [by rewrite all_map; apply/allP => v Hin /=; simp is_non_redundant| by apply: exec_filtered_queries_asdf].
  Qed.


  (*Lemma eval_filter_subseq k (qs : seq (@Query Name Vals)) u :
    subseq (⟦ filter_queries_with_label k qs ⟧ˢ in u) (⟦ qs ⟧ˢ in u).
    *)
    
 
   



 

  
  Theorem grounding_preserves_semantics ty u qs :
    u.(type) \in get_possible_types s ty ->
    ⟦ ground s ty qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
    elim: n qs u ty => /= [| n IH] qs u ty.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: qs => //; case=> [f α | l f α | f α φ | l f α φ | t φ] qs /= Hleq Hinpty; simp ground.
      * case is_object_type => /=; [simp execute_selection_set|].
        + case lookup_field_in_type => //=; last by apply: IH.
          by case (u.(fields) _) => /= [[v | vs] |]; rewrite filter_ground_swap IH //;
             have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.
        + simp try_inline_query.
          case: eqP => /= Heq.
          simp execute_selection_set.
          case lookup_field_in_type => //=; last by apply: IH.
          by case (u.(fields) _) => /= [[v | vs] |]; rewrite filter_ground_swap IH //;
             have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.

          admit. (* Inlining field *)
      * case is_object_type => /=; [simp execute_selection_set|].
        + case lookup_field_in_type => //=; last by apply: IH.
          by case (u.(fields) _) => /= [[v | vs] |]; rewrite filter_ground_swap IH //;
             have Hfleq := (filter_queries_with_label_leq_size l qs); ssromega.
        + simp try_inline_query.
          case: eqP => /= Heq.
          simp execute_selection_set.
          case lookup_field_in_type => //=; last by apply: IH.
          by case (u.(fields) _) => /= [[v | vs] |]; rewrite filter_ground_swap IH //;
             have Hfleq := (filter_queries_with_label_leq_size l qs); ssromega.
          admit. (* Inlining field *)

      * case Hlook : lookup_field_in_type => [fld|] /=.
        case Hscope: is_object_type => /=.
        have Hpty := (get_possible_types_objectE Hscope).
        have Hinpty2 := Hinpty.
        rewrite Hpty mem_seq1 /= in Hinpty2; move/eqP in Hinpty2.
        simp execute_selection_set; rewrite Hinpty2 Hlook /=.
        case: fld {Hlook} => f' args; case=> rty /=.
        case ohead => //= [v |].
        rewrite filter_ground_swap IH //.
        congr cons; congr pair; congr Object.
        admit. (* Subqueries with merging *)
        have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.
        rewrite filter_ground_swap IH //; have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.
        rewrite filter_ground_swap IH //; last by have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.
        
        congr cons; congr pair; congr Array.
        apply/eq_in_map => v Hin; congr Object.
        admit. (* Subqueries with merging *)
       
        + (* Inlining *)
          simp try_inline_query; case: eqP => /= Hpty; [admit |]. (* First one is similar to previous proof, but have to pay attention to abstract scope *)
          (* lookup f in u should give the same as looking up in ty. 
             Probably need more info, such as query and graph conformance to show that both 
             lookups result in the same field definition being fetched *)
          admit. (* Inline field *)

        + (* Error *)
          (* Similar to previous one, both lookups should result in the same, if
             the query and graph conforms. *)
          admit.

      * admit. (* Copy & Paste *)

      * case Hscope : is_object_type => /=.
        + case Hfapplies : does_fragment_type_apply => /=.
          (* fragment type applies *)
          simp execute_selection_set.
          have Hpty := (get_possible_types_objectE Hscope).
          have Hinpty2 := Hinpty.
          rewrite Hpty mem_seq1 /= in Hinpty2; move/eqP in Hinpty2.
          rewrite Hinpty2 Hfapplies /= -ground_cat; apply: IH => //; by rewrite queries_size_cat; rewrite -/(queries_size φ) in Hleq; ssromega.
          (* fragment type does not apply *)
          simp execute_selection_set.
          have Hinpty2 := Hinpty.
          have Hpty := (get_possible_types_objectE Hscope).
          rewrite Hpty mem_seq1 /= in Hinpty2; move/eqP in Hinpty2.
          rewrite Hinpty2 Hfapplies /=; apply: IH => //; ssromega.

        + case Ht : is_object_type => /=.
          case Hfapplies : does_fragment_type_apply => /=; simp execute_selection_set; case Huapplies : does_fragment_type_apply => /=.
          admit. (* Weird case :/ *)
          apply: IH => //; by ssromega.
          admit. (* Contradiction : if fragment applies between u & t → u = t → t ∈ possible types of ty → fragment applies between t and ty *)
          
          by apply: IH => //; ssromega.

          admit. (* Inlining with intersection of subtypes *)         
  Admitted.

 
  Lemma are_grounded_fields_grounded qs :
    are_grounded_fields s qs ->
    are_grounded s qs.
  Proof.
    elim: qs => //= q qs IH /and3P [Hfld Hg Hgs]; apply_andP.
    by rewrite Hfld /=.
  Qed.



  
  Lemma filter_queries_fragments_swap l t (qs : seq (@Query Name Vals)) :
    filter_queries_with_label l (filter_fragments_with_guard t qs) =
    filter_fragments_with_guard t (filter_queries_with_label l qs).
  Admitted.

  Lemma filter_fragments_when_all_fields_is_same t (qs : seq (@Query Name Vals)) :
    all (fun q => q.(is_field)) qs ->
    filter_fragments_with_guard t qs = qs.
  Proof.
    by funelim (filter_fragments_with_guard t qs) => //= /andP [_ Hflds]; rewrite H //.
  Qed.

  Lemma filter_fragments_cat t (qs1 qs2 : seq (@Query Name Vals)) :
    filter_fragments_with_guard t (qs1 ++ qs2) = 
    filter_fragments_with_guard t qs1 ++ filter_fragments_with_guard t qs2.
  Admitted.

  Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Name Vals)):
    filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
  Admitted.

   
    
  Lemma asdf q qs1 qs2 u :
    ⟦ qs1 ⟧ˢ in u = ⟦ qs2 ⟧ˢ in u ->
    ⟦ q :: qs1 ⟧ˢ in u = ⟦ q :: qs2 ⟧ˢ in u.
  Proof.
    by rewrite -2!cat1s; apply: qwe.
  Qed.
    
    

  

 

  
  Lemma filter_preserves_grounded_fields k qs :
    are_grounded_fields s qs ->
    are_grounded_fields s (filter_queries_with_label k qs).
  Proof.
      by funelim (filter_queries_with_label k qs) => //= /and3P [_ Hg Hgs]; do ?apply_and3P; apply: H.
  Qed.

  Lemma filter_preserves_grounded_inlines k qs :
    are_grounded_inlines s qs ->
    are_grounded_inlines s (filter_queries_with_label k qs).
  Proof.
    funelim (filter_queries_with_label k qs) => //=; simp is_grounded => /and3P [_ /andP [Hobj Hg] Hgs]; apply_and3P.
    by apply_andP; apply: filter_preserves_grounded_fields.
    by apply: H0.
  Qed.
  
  Lemma filter_preserves_grounded k qs :
    are_grounded s qs ->
    are_grounded s (filter_queries_with_label k qs).
  Proof.
    funelim (filter_queries_with_label k qs) => /=; simp is_field; simp is_grounded => /andP [Hg Hgs].
    case/andP: Hg; intros; apply_andP.
      by apply_andP; apply: filter_preserves_grounded_fields.
      by apply: filter_preserves_grounded_inlines.

      
      all: do ?[by apply_andP; apply: filter_preserves_grounded_fields].
      all: do ? [by apply: H; apply: are_grounded_fields_grounded].
  Qed.

  
  Lemma filter_preserves_grounded2 ty k qs :
    are_grounded2 s ty qs ->
    are_grounded2 s ty (filter_queries_with_label k qs).
  Proof.
    funelim (filter_queries_with_label k qs) => //=;
                                                 rewrite !are_grounded2_clause_2_equation_1;
                                                 case is_object_type; case: eqP => //= _; case/and3P; intros.

    all: do ? apply_and3P; simp is_grounded2. (* simp is_grounded also works... *)
    simp is_grounded2 in p0; case/andP: p0; intros.
    by apply_andP; apply: H.
  Qed.

  Theorem remove_redundancies_preserves_grounded2_semantics ty u qs :
    are_grounded2 s ty qs -> 
    ⟦ remove_redundancies qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    funelim (execute_selection_set u qs) => //=.

    - simp remove_redundancies; simp execute_selection_set; rewrite Heq /=. admit.
    - simp remove_redundancies; simp execute_selection_set; rewrite Heq0 /= Heq /=.
      rewrite filter_remove_swap filter_filter_absorb; intros. congr cons; apply: (H ty).
      apply: filter_preserves_grounded2. admit.
    - simp remove_redundancies; simp execute_selection_set; rewrite Heq0 /= Heq /=.
      rewrite filter_remove_swap filter_filter_absorb; intros. congr cons; apply: (H ty).
      apply: filter_preserves_grounded2. admit.
    - simp remove_redundancies; simp execute_selection_set; rewrite Heq0 /= Heq /=.
      rewrite filter_remove_swap filter_filter_absorb; intros. congr cons; apply: (H ty).
      apply: filter_preserves_grounded2. admit.

    - admit.
    - admit.
    - admit.
    - admit.

    - admit.
    - intros.
      simp remove_redundancies; simp execute_selection_set; rewrite Heq0 /= Heq /=.
      congr cons; last first.
      rewrite filter_remove_swap filter_filter_absorb; apply: (H0 ty); admit.
      congr pair; congr Array; apply/eq_in_map => v Hin; congr Object.
      have ->: (find_queries_with_label s s3 v.(type) (remove_redundancies (filter_queries_with_label s3 l))) = [::] by admit.
      simp merge_selection_sets; rewrite cats0.
      rewrite -(find_queries_or_fields_is_same_if_all_fields v.(type)).
      apply: H.
      admit. (* are subqueries grounded - should be *)
      admit. (* are all fields in list ? - yes *)

    - intros.
      simp remove_redundancies; simp execute_selection_set; rewrite Heq1 /= Heq0 /= Heq /=.
      congr cons; last first.
      rewrite filter_remove_swap filter_filter_absorb; apply: (H0 ty); admit.
      congr pair; congr Object.
      have ->: (find_queries_with_label s s3 n.(type) (remove_redundancies (filter_queries_with_label s3 l))) = [::] by admit.
      simp merge_selection_sets; rewrite cats0.
      rewrite -(find_queries_or_fields_is_same_if_all_fields n.(type)).
      apply: (H f.(return_type)).
      admit.
      admit.

    - intros.
      simp remove_redundancies; simp execute_selection_set; rewrite Heq1 /= Heq0 /= Heq /=; congr cons.
      rewrite filter_remove_swap filter_filter_absorb; apply: (H ty). admit.

    - admit.
    - admit.
    - admit.
    - admit.

    - intros; simp remove_redundancies; simp execute_selection_set; rewrite Heq /=.
      admit.

    - intros; simp remove_redundancies; simp execute_selection_set; rewrite Heq /=.

  Abort.


  Theorem remove_redundancies_preserves_grounded2_semantics ty u qs :
    are_grounded2 s ty qs -> 
    ⟦ remove_redundancies qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    funelim (remove_redundancies qs) => //=; rewrite are_grounded2_clause_2_equation_1.
    - case Hscope : is_object_type; case: eqP => //= Hpty => /and3P [_ _ Hgs].
      * simp execute_selection_set; case Hlook : lookup_field_in_type => //= [fld|].
        + by case (u.(fields) _) => /= [[v | vs] |]; congr cons; rewrite filter_remove_swap filter_filter_absorb;
                                     apply: (H ty) => //; apply: filter_preserves_grounded2.
          (* lookup = null then semantics is the same *)
          admit.

      * simp execute_selection_set; case Hlook : lookup_field_in_type => //= [fld|].
        + by case (u.(fields) _) => /= [[v | vs] |]; congr cons; rewrite filter_remove_swap filter_filter_absorb;
                                     apply: (H ty) => //; apply: filter_preserves_grounded2.
          (* lookup = null then semantics is the same *)
          admit.

    - admit. (* Copy & Paste *)

    - case Hscope : is_object_type; case: eqP => //= Hpty /and3P [_ Hg Hgs]; simp execute_selection_set.
      * case Hlook : lookup_field_in_type => [fld |] /=.
        case fld.(return_type) => /= rty.

        + case ohead => [v |] /=.
          congr cons; last first.
          rewrite filter_remove_swap filter_filter_absorb; apply: (H0 ty).  H0 //.
          congr pair; congr Object.
      
        
  Theorem remove_redundancies_preserves_semantics u qs :
    are_grounded s qs -> 
    ⟦ remove_redundancies qs ⟧ˢ in u = ⟦ qs ⟧ˢ in u.
  Proof.
    funelim (remove_redundancies qs) => //=.
    - simp is_field => /=; rewrite -/(are_grounded_fields s l) => /andP [Hg Hgflds].
      simp execute_selection_set; case Hlook : lookup_field_in_type => //= [fld|].
      * case (u.(fields) _) => /= [[v | vs] |]; congr cons; rewrite filter_remove_swap filter_filter_absorb;
        by apply: H => //; apply: are_grounded_fields_grounded; apply: filter_preserves_grounded_fields.
      * rewrite H //; last by apply: filter_preserves_grounded; apply: are_grounded_fields_grounded.
        (* lookup = null then semantics is the same *)
        admit.
        
    - simp is_field => /=; rewrite -/(are_grounded_fields s l) => /andP [Hg Hgflds].
      simp execute_selection_set; case Hlook : lookup_field_in_type => //= [fld|].
     * case (u.(fields) _) => /= [[v | vs] |]; congr cons; rewrite filter_remove_swap filter_filter_absorb;
        by apply: H => //; apply: are_grounded_fields_grounded; apply: filter_preserves_grounded_fields.
      * rewrite H //; last by apply: filter_preserves_grounded; apply: are_grounded_fields_grounded.
        (* lookup = null then semantics is the same *)
        admit.
    

    - simp is_field => /=; rewrite -/(are_grounded_fields s l); simp is_grounded => /andP [Hg Hgflds].
      simp execute_selection_set.
      case Hlook : lookup_field_in_type => [fld|] //=.
      * case fld.(return_type) => rty /=; [|congr cons].
        + case ohead => /= [v |]; congr cons. 
          congr pair; congr Object.
          rewrite !find_queries_or_fields_is_same_if_all_fields.
          have ->: (find_fields_with_response_name Name Vals s3
                                                   (remove_redundancies (filter_queries_with_label s3 l))) = [::] by admit.
          simp merge_selection_sets; rewrite cats0 H //.
          rewrite are_grounded_cat.
          (* are subqueries grounded ? -> yep, should be simple *)
          admit.
            by rewrite are_grounded_fields_E in Hgflds; case/andP: Hgflds.
            admit. (* remove redundancies preserves fields *)
            
            rewrite filter_remove_swap filter_filter_absorb; apply: H0.
            admit. (* filter preserves grounding *)

            rewrite filter_remove_swap filter_filter_absorb; apply: H0.
            admit.

        + congr pair; congr Array.
          apply/eq_in_map => v Hin; congr Object.
          rewrite !find_queries_or_fields_is_same_if_all_fields.
          have ->: (find_fields_with_response_name Name Vals s3
                                                   (remove_redundancies (filter_queries_with_label s3 l))) = [::] by admit.
          simp merge_selection_sets; rewrite cats0 H //.
           (* are subqueries grounded ? -> yep, should be simple *)
          admit.
          by rewrite are_grounded_fields_E in Hgflds; case/andP: Hgflds.
          admit. (* remove redundancies preserves fields *)
            
          rewrite filter_remove_swap filter_filter_absorb; apply: H0.
          admit.
          admit.

    - simp is_field => /=; rewrite -/(are_grounded_fields s l); simp is_grounded => /andP [Hg Hgflds].
      simp execute_selection_set.
      case Hlook : lookup_field_in_type => [fld|] //=.
      * case fld.(return_type) => rty /=; [|congr cons].
        + case ohead => /= [v |]; congr cons. 
          congr pair; congr Object.
          rewrite !find_queries_or_fields_is_same_if_all_fields.
          have ->: (find_fields_with_response_name Name Vals s4
                                                   (remove_redundancies (filter_queries_with_label s4 l))) = [::] by admit.
          simp merge_selection_sets; rewrite cats0 H //.
          (* are subqueries grounded ? -> yep, should be simple *)
          admit.
            by rewrite are_grounded_fields_E in Hgflds; case/andP: Hgflds.
            admit. (* remove redundancies preserves fields *)
            
            rewrite filter_remove_swap filter_filter_absorb; apply: H0.
            admit. (* filter preserves grounding *)

            rewrite filter_remove_swap filter_filter_absorb; apply: H0.
            admit.

        + congr pair; congr Array.
          apply/eq_in_map => v Hin; congr Object.
          rewrite !find_queries_or_fields_is_same_if_all_fields.
          have ->: (find_fields_with_response_name Name Vals s4
                                                   (remove_redundancies (filter_queries_with_label s4 l))) = [::] by admit.
          simp merge_selection_sets; rewrite cats0 H //.
           (* are subqueries grounded ? -> yep, should be simple *)
          admit.
          by rewrite are_grounded_fields_E in Hgflds; case/andP: Hgflds.
          admit. (* remove redundancies preserves fields *)
            
          rewrite filter_remove_swap filter_filter_absorb; apply: H0.
          admit.
          admit.

    - simp is_field; rewrite -/(are_grounded_inlines s l); simp is_grounded => /andP [/andP [Htobj Hgflds] Hginls].
      simp execute_selection_set.
      case Hfapplies : does_fragment_type_apply => //=.
      admit.

      (* removing invalid fragments preserves semantics *)
      rewrite H0.
      apply: filtering_invalid_fragments_preserves_semantics => //.
      admit.






          
  
    
  Lemma fragment_applies_for_node u : does_fragment_type_apply s u.(type) u.(type). Admitted.
  
  Lemma normalize_preserves_semantics ty u qs :
    ⟦ normalize s ty qs in u ⟧ˢ = ⟦ qs in u ⟧ˢ.
  Proof.
    rewrite /normalize /=.
    rewrite (remove_redundancies_preserves_semantics u (ground s ty qs)).
    by rewrite grounding_preserves_semantics.
  Qed.
  


  
  Reserved Notation "⦃ queries 'in' u ⦄" (at level 50).
  
   Equations? execute_selection_set2 u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];

      execute_selection_set2 u (SingleField f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (f, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
        | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
        | None => (f, Leaf Null) :: ⦃ qs in u ⦄
        };
      
      execute_selection_set2 u (LabeledField l f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (l, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
        | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
        | None => (l, Leaf Null) :: ⦃ qs in u ⦄
        };

      
      execute_selection_set2 u (NestedField f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (f, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (f, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
            
            | _ =>  (f, Leaf Null) :: ⦃ qs in u ⦄
            };

        | None => (f, Leaf Null) :: ⦃ qs in u ⦄
        };

       execute_selection_set2 u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (l, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (l, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
            
            | _ =>  (l, Leaf Null) :: ⦃ qs in u ⦄
            };

        | None => (l, Leaf Null) :: ⦃ qs in u ⦄
        };

       
        execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⦃ φ ++ qs in u ⦄;
        | _ := ⦃ qs in u ⦄
        }

    }
   where "⦃ queries 'in' u ⦄" := (execute_selection_set2 u queries).
   all: do ? by ssromega.
   all: do [by rewrite ?queries_size_cat -/(queries_size φ); ssromega].
  Qed.

 
  Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Name Vals)) :
    filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
  Proof.
    elim: qs1  => //= hd tl IH.
    case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
    by rewrite IH.
  Qed.

  (*
  Lemma normalize_filter_swap label ty qs :
    is_object_type s ty ->
    filter_queries_with_label label (normalize__φ s ty qs) = normalize__φ s ty (filter_queries_with_label label qs).
  Proof.
    move=> Hscope.
    move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
    elim: n qs => //= [| n IH].
    - admit.
    - case=> //; case=> [f α | l f α | f α φ | l f α φ | t φ] qs /= Hleq;
                            simp normalize; rewrite ?Hscope /=; simp filter_queries_with_label => /=.

    all: do ?[by case: eqP => //= Heq; simp normalize; rewrite Hscope /= IH].

    * case Hlook : lookup_field_in_type => [fld|] //=; rewrite ?Hscope /=; simp filter_queries_with_label => /=.
      case: eqP => //= Heq; simp normalize.
      + rewrite IH //; ssromega. 
      + rewrite Hlook /= Hscope /= IH //; ssromega.
      + case: eqP => //= Heq; simp normalize; rewrite ?Hlook /= IH //; ssromega.

    * case Hlook : lookup_field_in_type => [fld|] //=; rewrite ?Hscope /=; simp filter_queries_with_label => /=.
      case: eqP => //= Heq; simp normalize.
      + rewrite IH //; ssromega. 
      + rewrite Hlook /= Hscope /= IH //; ssromega.
      + case: eqP => //= Heq; simp normalize; rewrite ?Hlook /= IH //; ssromega.


    * simp normalize; rewrite Hscope /= filter_queries_with_label_cat.
      rewrite (IH qs) //; do ? ssromega.
      rewrite (IH φ) //; rewrite -/(queries_size φ) in Hleq; ssromega.
  Admitted.     

  Lemma lookup_field_return_type ty f fld :
    lookup_field_in_type s ty f = Some fld ->
    lookup_field_type s ty f = Some (fld.(return_type)).
  Admitted.
*)
   
  Transparent is_field is_inline_fragment qresponse_name qsubqueries.

  Lemma are_similar_fields_share_response_name (q1 q2 : @Query Name Vals) (Hfield1 : q1.(is_field)) (Hfield2 : q2.(is_field)) :
    are_similar q1 q2 -> (qresponse_name q1 Hfield1) == (qresponse_name q2 Hfield2).
  Proof.
    funelim (are_similar q1 q2) => //=.
  Qed.

   Lemma are_N_similar_fields_N_response_name (q1 q2 : @Query Name Vals) (Hfield1 : q1.(is_field)) (Hfield2 : q2.(is_field)) :
     ~~are_similar q1 q2 -> (qresponse_name q1 Hfield1) != (qresponse_name q2 Hfield2).
  Proof.
    funelim (are_similar q1 q2) => //=.
  Qed.

  
  Lemma filter_not_similar_preserves_list (q : @Query Name Vals) qs (Hfield : q.(is_field)) :
    all (fun q' => ~~are_similar q' q) qs ->
    all (fun q' => q'.(is_field)) qs ->
    filter_queries_with_label (qresponse_name q Hfield) qs = qs.
  Proof.
    funelim (filter_queries_with_label _ qs) => //= /andP [Hsim Hall] Hfields; do ? by rewrite H.

    all: do ?[have := (are_N_similar_fields_N_response_name _ q _ Hfield Hsim) => /=-/(_ is_true_true) Hcontr;
                by rewrite Hcontr in Heq].
  Qed.

  Lemma find_not_similar_is_nil ty (q : @Query Name Vals) qs (Hfield : q.(is_field)) :
    all (fun q' => ~~are_similar q' q) qs ->
    all (fun q' => q'.(is_field)) qs ->
    find_queries_with_label s ty (qresponse_name q Hfield) qs = [::].
  Proof.
  Admitted.

  Lemma asdf qs : all (fun q => q.(is_field)) qs ->
                  all (is_in_normal_form s) qs ->
                  are_in_normal_form s qs.
  Admitted.



 

    
  Lemma all_invalid_fragments_exec u φ qs :
    all (fun q => q.(is_inline_fragment)) qs ->
    are_in_normal_form s qs ->
    all (fun q => ~~are_similar q (InlineFragment u.(type) φ)) qs ->
    ⟦ φ ++ qs in u ⟧ˢ = ⟦ φ in u ⟧ˢ. 
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ qs => [| n IH] φ qs Hleq.
    - admit.
    -admit.
  Admitted.



  
  Lemma execute_selection_set_on_nrgt u qs :
    are_non_redundant qs ->
    are_in_normal_form s qs ->
    ⟦ qs in u ⟧ˢ = flatten [seq ⟦ [:: q] in u ⟧ˢ | q <- qs].
  Proof.
    Abort.
    
        
  Theorem execs_on_nrgtnf_are_equivalent u φ :
    are_in_normal_form s φ ->
    are_non_redundant φ ->
    ⦃ φ in u ⦄ = ⟦ φ in u ⟧ˢ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => [| n IH] φ u.
    - by rewrite leqn0 => /queries_size_0_nil ->. 
    - case: φ => //=; case=> /= [f α | l f α | f α φ | l f α φ | t φ] qs Hleq.
      * simp are_in_normal_form => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (SingleField f α)) // IH //; by apply: asdf.
      
      * simp are_in_normal_form => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (LabeledField l f α)) // IH //; by apply: asdf.

        
      * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
          by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
          by rewrite IH //; ssromega.
          
        + rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //. 
          congr cons; last by apply: IH => //; ssromega.
          congr pair; congr Array.
          apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
        + by rewrite IH //; ssromega.
             
      * simp are_in_normal_form => /and3P [Hnf Hfields Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
          by rewrite IH //; ssromega.
         
        + rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. 
          congr cons; last by apply: IH => //; ssromega.
          congr pair; congr Array.
          apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
            by rewrite cats0 !IH //; rewrite -/(queries_size φ) in Hleq; ssromega.
        + by rewrite IH //; ssromega. 

      * simp are_in_normal_form => /and5P [Hobj Hflds Hnf Hinl Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].
        simp execute_selection_set; simp execute_selection_set2.
        case Hfrag: does_fragment_type_apply => //=; last by apply: IH => //; ssromega.
        rewrite execute_selection_set2_cat.
        rewrite (all_invalid_fragments_eval u φ qs) // ?cats0; last first.
        rewrite /does_fragment_type_apply Hobj in Hfrag.
          by move/eqP in Hfrag; rewrite Hfrag.        
        
          
        rewrite all_invalid_fragments_exec //; [apply: IH => //; rewrite -/(queries_size φ) in Hleq; ssromega|].
        rewrite /does_fragment_type_apply Hobj in Hfrag.
          by move/eqP in Hfrag; rewrite Hfrag.
  Qed.
  

        
  
  Theorem execs_are_equivalent u φ :
    all (has_valid_fragments s u.(type)) φ ->
    (⦃ (remove_redundancies s u.(type) (normalize__φ s u.(type) φ)) in u ⦄) = (⟦ φ in u ⟧ˢ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => /= [| n IH].
    - admit.
    - move=> φ u Hleq Hin; have Hscope := (node_in_graph_has_object_type Hin).
      case: φ Hleq => //.
      case=> [f α | l f α | f α φ | l f α φ | t φ] qs /= Hleq -/andP [Hv Hvs]; simp normalize;
              rewrite ?Hscope /=; simp remove_redundancies; simp execute_selection_set.

      * simp execute_selection_set2.
        case : (u.(fields) _) => //=.
        + case=> //= v; rewrite normalize_filter_swap // IH //;
                             do ?[by have Hleq2 := (filter_queries_with_label_leq_size f qs); ssromega].
          admit.
          admit.
        + rewrite normalize_filter_swap // IH //; [by have Hleq2 := (filter_queries_with_label_leq_size f qs); ssromega|].
          admit.
      * simp execute_selection_set2.
        case : (u.(fields) _) => //=.
        + case=> //= v; rewrite normalize_filter_swap // IH //;
                             do ?[by have Hleq2 := (filter_queries_with_label_leq_size l qs); ssromega].
          admit.
          admit.
        + rewrite normalize_filter_swap // IH //; [by have Hleq2 := (filter_queries_with_label_leq_size l qs); ssromega|].
          admit.

      * case Hlook: lookup_field_in_type => [fld|] //=.
        rewrite Hscope /=; simp remove_redundancies; simp execute_selection_set2.
        case: fld Hlook => f' args rty Hlook; rewrite Hlook /=.
        simp execute_selection_set2. rewrite Hlook /=.
        case: rty Hlook => //= ty Hlook.
        + case ohead => //= [v|].
          congr cons; last first.
          rewrite normalize_filter_swap //.
          admit.
          
          IH //. admit. admit.
          rewrite normalize_filter_swap // IH.
   

  Equations resolve_field_value u (field_name : Name) (argument_values : {fmap Name -> Vals}) : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals)) :=
    {
      resolve_field_value u f α
        with u.(fields) (Field f α) :=
        {
        | Some value := Some (inl (inl value));
        | _ with neighbours_with_field g u (Field f α) :=
            {
            | [::] := None;
            | [:: v] => Some (inl (inr v));
            | vs := Some (inr vs)
            }
        }
    }.


  Equations? execute_selection_set2 u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];
      
      execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply u.(type) t :=
        {
        | true := execute_selection_set u (φ ++ qs);
        | _ := execute_selection_set u qs
        };

      execute_selection_set2 u (q :: qs)
        with lookup_field_type s u.(type) (qname q _) :=
        {
        | Some (ListType ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _)))
                         :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)

           where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode :=
                   {
                     complete_value None := Leaf Null;

                     complete_value (Some (inr vs)) := Array
                                                        [seq Object
                                                             (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label v.(type) (qresponse_name q _) qs))) | v <- vs];

                     complete_value _ := Leaf Null
                   };

        | Some (NT ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _)))
                         :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)

           where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode :=
                   {
                     complete_value None := Leaf Null;

                     complete_value (Some (inl (inl value)))
                       with value :=
                       {
                       | inl v := Leaf (SingleValue v);
                       | inr vs := Array (map (Leaf \o SingleValue) vs)
                       };

                     complete_value (Some (inl (inr v))) := Object (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label v.(type) (qresponse_name q _) qs)));

                     complete_value _ := Leaf Null
                   };

        | _ := ((qresponse_name q _), Leaf Null) :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)
        }
    }.
  Proof.
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown3 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown5 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown2 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown8 qs); ssromega].
    
    - by have Hleq := (filter_queries_with_label_leq_size unknown1 qs); ssromega.
    - by have Hleq := (filter_queries_with_label_leq_size unknown7 qs); ssromega.
    - by have Hleq := (filter_queries_with_label_leq_size unknown11 qs); ssromega.
  Qed.

  
  
  

        
End QuerySemantic.

Arguments β [Name Vals].
Arguments collect [Name Vals].
Arguments eval [Name Vals].
Arguments eval_queries [Name Vals].
