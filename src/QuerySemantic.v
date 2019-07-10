Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
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


Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  
  Variable s : @wfSchema Name Vals.
  Variable g : @conformedGraph Name Vals s.
  
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type queries : seq (@Query Name Vals).

  Transparent qresponse_name.

 

 
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
    all: do [simp query_size; do ? ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size f qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size l qs); ssromega].
  
    all: do ?[by rewrite queries_size_app;
            have Hleq1 := (found_queries_leq_size s f u.(type) qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label s f u.(type) qs)); ssromega].

    all: do ?[by rewrite queries_size_app;
            have Hleq1 := (found_queries_leq_size s l u.(type) qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label s l u.(type) qs)); ssromega].


    all: do ? [by rewrite ?queries_size_app; ssromega].
  Qed.

   



  Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Query Name Vals)) :
    merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
  Admitted.
  
  Reserved Notation "ty '⊢' φ '≡' φ'" (at level 80).

  
  Inductive Equiv (ty : Name) : seq Query -> seq (@Query Name Vals) -> Prop :=
  | ENil : ty ⊢ [::] ≡ [::]
              
  | ESF : forall f α φ φ',
      ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ'  ->
      ty ⊢ SingleField f α :: φ ≡ SingleField f α :: φ' 
         
 
  | ENF1 : forall f α β χ fld φ φ',
      lookup_field_in_type s ty f = Some fld ->
      (forall t, t \in get_possible_types s fld.(return_type) ->
                  t ⊢ β ++ merge_selection_sets (find_queries_with_label s f ty φ) ≡
                    χ ++ merge_selection_sets (find_queries_with_label s f ty φ')) ->
      
      ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ' ->
      ty ⊢ NestedField f α β :: φ ≡ NestedField f α χ :: φ' 

  | ENF2 : forall f α β χ φ φ',
      lookup_field_in_type s ty f = None ->
      ty ⊢ φ ≡ φ'  ->
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


  Lemma equiv_sym ty φ φ' :
    ty ⊢ φ ≡ φ' ->
    ty ⊢ φ' ≡ φ.
  Proof.
    elim; intros.
    - by constructor.
    - by constructor.
    - apply: ENF1 => //=.
      * exact: H.
      * by apply: H1.

    - by apply: ENF2 => //=.

    - by apply: EIF12 => //=.
    - by apply: EIF11 => //=.
    - by apply: EIF22 => //=.
      by apply: EIF21 => //=.
  Qed.

  Hint Constructors Equiv.
  Hint Resolve queries_size_app.
  Lemma equiv_refl ty φ : ty ⊢ φ ≡ φ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => //= [| n IH] ty φ; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
    case: φ; first by intros; constructor.
    case=> //= [f α | | f α β | | t β] φ; simp query_size => Hleq.
    - by constructor; apply: IH; have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
    - admit. (* Label *)
    - case Hlook : (lookup_field_in_type s ty f) => [fld|] //=; [apply: ENF1 | apply: ENF2 => //].
      * exact: Hlook.
      * move=> t Hin.
        apply: IH => /=.
        rewrite queries_size_app.
        admit. (* leq size *)
        apply: IH.
        admit. (* leq size *)
      * apply: IH; ssromega.

    - admit. (* Labeled *)

    - case Hspread : (does_fragment_type_apply s ty t) => //=; [apply: EIF11 => //= | apply: EIF21 => //=].
      * apply: equiv_sym.
        apply: EIF11 => //=.
        apply: IH => //=.
        rewrite queries_size_app; ssromega.

      * apply: equiv_sym.
        apply: EIF21 => //=; apply: IH; ssromega.
  Admitted.

  Hint Resolve equiv_refl.
    

  Lemma equiv_trans ty φ1 φ2 φ3 :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ φ2 ≡ φ3 ->
    ty ⊢ φ1 ≡ φ3.
  Proof.
  Admitted.

  

  Lemma equiv_cat_hd ty φ1 φ1' φ :
    ty ⊢ φ1 ≡ φ1' ->
    ty ⊢ φ1 ++ φ ≡ φ1' ++ φ.
  Proof.
    move=> Heq.
    elim: Heq φ => //=.
    - intros; constructor.
      by rewrite !filter_queries_with_label_cat; apply: H0.

    - intros; apply: ENF1 => //=.
      exact: H.
      intros.
      rewrite !find_queries_with_label_cat !merge_selection_sets_cat !catA.
      apply: H1 => //=.
      rewrite !filter_queries_with_label_cat; apply: H3.

    - by intros; apply: ENF2.
      
    - intros; apply: EIF11 => //=.
      by rewrite catA; apply: H1.

    - by intros; apply: EIF12 => //=; rewrite catA; apply: H1.

    - by intros; apply: EIF21.

    - by intros; apply: EIF22.
  Qed.



   Lemma filter_ground_swap k ty qs :
    filter_queries_with_label k (ground s ty qs) = ground s ty (filter_queries_with_label k qs).
  Admitted.

   Lemma filter_remove_swap k (qs : seq (@Query Name Vals)) :
    filter_queries_with_label k (remove_redundancies qs) = remove_redundancies (filter_queries_with_label k qs).
  Admitted.



  Lemma find_queries_or_fields_is_same_if_all_fields ty label qs :
    all (fun q => q.(is_field)) qs ->
    find_queries_with_label s label ty qs = find_fields_with_response_name Name Vals label qs.
  Proof.
    elim: qs => //= q qs IH /andP [Hfield Hfields].
    case: q Hfield => //= [f α | l f α | f α φ | l f α φ] _.

    all: do ?[by simp find_queries_with_label; simp find_fields_with_response_name;
              case: eqP => //= _; [congr cons |]; apply: IH].
  Qed.
  
  Lemma filter_preserves_equiv ty f φ φ' :
    ty ⊢ φ ≡ φ' ->
    ty ⊢ filter_queries_with_label f φ ≡ filter_queries_with_label f φ'.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty f φ φ' => //= [| n IH] ty f φ φ'.
    - rewrite leqn0 => /queries_size_0_nil ->.
      admit.

    - case: φ => //=.
    - admit.
    - case=> [f' α | | f' α β | | t β] φ; simp query_size => /= Hleq.

    - move=> Heq; inversion Heq.
      * simp filter_queries_with_label; case: eqP => //= Hfeq.
        by rewrite -Hfeq.
        constructor.
        rewrite filter_swap //.
        rewrite [X in ty ⊢ filter_queries_with_label f _ ≡ X]filter_swap //.
        apply IH => //=.
        admit.
      * simp filter_queries_with_label; case: eqP => //= Hfeq.
        apply: EIF12 => //=.
        rewrite -filter_queries_with_label_cat; apply: IH => //=.
        

  Admitted.

        
  Lemma equiv_cat_tail ty φ1 φ2 φ :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ φ ++ φ1 ≡ φ ++ φ2.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ φ1 φ2 => //= [| n IH] ty φ φ1 φ2.
    by rewrite leqn0 => /queries_size_0_nil ->; rewrite 2!cat0s.
    case: φ => //=; case=> [f α | | f α β | | t β] φ; simp query_size => /= Hleq.

    - intros; constructor.
      by apply: filter_preserves_equiv; apply: IH.

    - admit. (* Labeled *)

    - intros; case Hlook : (lookup_field_in_type s ty f) => [fld|] /=.
      * apply: ENF1 => //=; first exact: Hlook.
        intros.
        apply IH => //=; first by ssromega.
        rewrite 2!find_queries_with_label_cat 2!merge_selection_sets_cat.
        apply IH => //=.
        admit. (* merge size ≤ n *)
        admit. (* merge preserves equiv *)
        
        by apply: filter_preserves_equiv; apply: IH => //; ssromega.

      * apply: ENF2 => //=; apply: IH => //=; ssromega.

    - admit. (* Labeled *)

    - intros; case Hfapplies : (does_fragment_type_apply s ty t).
      * apply: EIF11 => //=.
        apply: EIF12 => //=; rewrite 2!catA.
        apply: IH => //=.
        by rewrite queries_size_app; ssromega.

      * apply: EIF21 => //=.
        apply: EIF22 => //=.
        by apply: IH => //=; ssromega.

  Admitted.

    
  Theorem equiv_cat ty φ φ' β β' :
    ty ⊢ φ ≡ φ' ->
    ty ⊢ β ≡ β' ->
    ty ⊢ φ ++ β ≡ φ' ++ β'.
  Proof.
    move=> Heq1 Heq2.
    have Heq11 := (equiv_cat_hd ty φ φ' β Heq1).
    have Heq22 := (equiv_cat_tail ty β β' φ' Heq2).
    apply: equiv_trans.
    exact: Heq11.
    exact: Heq22.
  Qed.


   Lemma empty_frag_equiv_nil ty tys (φ : seq (@Query Name Vals)) :
    ty ⊢ [seq InlineFragment t [::] | t <- tys] ≡ [::].
   Proof.
     elim: tys => //= t tys IH.
     case Hfapplies : (does_fragment_type_apply s ty t) => /=; [by apply: EIF11 | by apply: EIF21].
   Qed.

   Lemma filter_frag (qs : seq (@NamedType Name)) f α :
     @filter_queries_with_label Name Vals f [seq InlineFragment t0 [:: SingleField f α] | t0 <- qs] =
     [seq InlineFragment t0 [::] | t0 <- qs].
   Proof.
     elim: qs => //= q qs IHqs; simp filter_queries_with_label => /=; case: eqP => //= _; simp filter_queries_with_label.
          by rewrite IHqs.
   Qed.


  Lemma find_ground_swap ty f φ :
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

  
  Lemma find_equiv ty f φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    ty ⊢ find_queries_with_label s f ty φ1 ≡ find_queries_with_label s f ty φ2.
  Admitted.
    
  Lemma merge_ground_swap ty fld φ :
    is_object_type s ty ->
    all (fun q => match q with
               | SingleField f _
               | LabeledField _ f _
               | NestedField f _ _
               | NestedLabeledField _ f _ _ => lookup_field_in_type s ty f == Some fld
               | _ => false
               end) φ ->
    merge_selection_sets (ground s ty φ) = ground s fld.(return_type) (merge_selection_sets φ).
  Proof.
    move=> Hscope.
    elim: φ fld => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH fld /andP; last by case.
    
  Admitted.
  
  Lemma merge_ble ty φ1 φ2 :
    ty ⊢ φ1 ≡ φ2 ->
    all (fun q => q.(is_field)) φ1 ->
    all (fun q => q.(is_field)) φ2 ->
    ty ⊢ merge_selection_sets φ1 ≡ merge_selection_sets φ2.
  Proof.
    elim => //=.

    - intros; simp merge_selection_sets => /=.
      admit.
    - intros.
      simp merge_selection_sets => /=.
  Admitted.
    
    
  Lemma ground_equiv1 ty φ1 φ2 :
    forall t, t \in get_possible_types s ty ->
               t ⊢ φ1 ≡ φ2  ->
               t ⊢ ground s ty φ1 ≡ φ2.
  Proof. 
    move: {2}(queries_size _) (leqnn (queries_size φ1)) => n.
    elim: n ty φ1 φ2 => //= [| n IH] ty φ1 φ2.
    - rewrite leqn0 => /queries_size_0_nil -> t Hin; simp ground.

    - move=> Hleq t Hin Heq.
      move: Hleq; inversion Heq => //=; simp query_size => Hleq; simp ground.

    (* f[α] : _ ≡ f[α] *)
    - case Hscope : is_object_type => //=.
      (* ty ∈ Ot *)
      * constructor.
        rewrite filter_ground_swap.
        apply: IH => //=.
        by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.

          
      (* ty ∈ At *)
      * have : forall tys,
          t \in tys ->
                t ⊢ [seq InlineFragment t' [:: SingleField f α] | t' <- tys] ++ ground s ty φ ≡ SingleField f α :: φ'.
        elim=> //= t' tys IHtys.
        rewrite inE => /orP [/eqP Hteq | Htin].
        rewrite -Hteq.
        apply: EIF11 => //=.
        admit. (* fragment applies to itself *)
        constructor.
        rewrite filter_queries_with_label_cat.
        rewrite filter_frag filter_ground_swap.
        apply: equiv_trans.
        apply: equiv_cat_hd.
        exact: empty_frag_equiv_nil.
        rewrite cat0s.
        apply: IH => //=.
          by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.
        case Hfapplies : (does_fragment_type_apply s t t').
        apply: EIF11 => //=.    
        constructor; rewrite filter_queries_with_label_cat filter_ground_swap filter_frag.
        apply: equiv_trans.
          by apply: equiv_cat_hd; apply: empty_frag_equiv_nil.
        rewrite cat0s; apply: IH => //=; by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.

        by apply: EIF21 => //=; apply: IHtys.
        
        by move/(_ (get_possible_types s ty) Hin).
          
          
    (* Case ENF1 : f[α] { β_1 ... β_k } : _ ≡ f[α] { χ_1 ... χ_m } : _ *)
    - case Hlook : lookup_field_in_type => [fld'|] /=.

      * case Hscope : is_object_type => /=.
        (* ty ∈ Ot *)
        + apply: ENF1 => //=; first exact: H.
          move=> t' Hinrty.
          have Httyeq : t = ty by rewrite (get_possible_types_objectE Hscope) /= mem_seq1 in Hin; apply/eqP.
          rewrite Httyeq in IH H H0 Hlook *.
          have Htrans : t' ⊢ ground s fld'.(return_type) β ++ merge_selection_sets (find_queries_with_label s f ty (ground s ty φ)) ≡
                                                       β ++ merge_selection_sets (find_queries_with_label s f ty φ).
          apply: equiv_cat.
          by apply: IH => //=; [ ssromega | rewrite Hlook in H; case: H => ->].
          
          
          admit. (* subqueries are equivalent *)

          apply: equiv_trans; first exact: Htrans.
          by apply: H0.
          rewrite filter_ground_swap; apply: IH => //=.
            by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.

        + have Htrans :
            forall ptys,
              t ⊢ [seq InlineFragment t0 [:: NestedField f α (ground s (return_type fld') β)] | t0 <- ptys] ++ ground s ty φ
                ≡
                InlineFragment t [:: NestedField f α β] :: φ.
          admit.
          apply: equiv_trans.
          apply: Htrans.
          apply: EIF11 => //=.
          admit.
          apply: ENF1; first exact: H.
          exact: H0.
          exact: H1.
                    

      (* lookup = Null *) 
      * admit.


    (* Case ENF2 : f[α] { β_1 ... β_k } : _ ≡ f[α] { χ_1 ... χ_m } : _ *)
    - case Hlook : lookup_field_in_type => [fld |] //=.
      case Hscope : is_object_type => /=.
      (* ty ∈ Ot *)
      * have Httyeq : t = ty by rewrite (get_possible_types_objectE Hscope) /= mem_seq1 in Hin; apply/eqP.
          by rewrite Httyeq Hlook in H.

      (* ty ∈ At *)
      * (* Contradiction : field is found in ty but not in implementation *)
        admit.

      * admit. (* lookup = null *)


    (* Case EIF11 *)
    - case Hscope : is_object_type => //=.
      (* ty ∈ Ot *)
      * have Httyeq : t = ty by rewrite (get_possible_types_objectE Hscope) /= mem_seq1 in Hin; apply/eqP.
        rewrite -Httyeq H /= -ground_cat.
        apply: IH => //=; first by rewrite queries_size_app; ssromega.
        by rewrite {2}Httyeq.
        
      (* ty ∈ At *)
      * case Ht : is_object_type => /=.
        (* t' ∈ Ot *)
        have Hteq : t0 = t by admit. (* Both are the same object *)
        rewrite Hteq.
        have Hfapplies : does_fragment_type_apply s t ty by admit. (* t <: ty *)
        rewrite Hfapplies /=.
        apply: EIF11 => //=.
        admit. (* t <: t *)
        apply: equiv_trans.
        apply: equiv_cat.
        apply: IH => //=; [by ssromega|].
        admit. (* t <: t *)
          by apply: IH => //=; ssromega.
          exact: H0.

      (* t' ∈ At *)
      + apply: equiv_trans.
        apply: (equiv_cat t _ (ground s t β)).
        have /(_ (get_possible_types s ty :&: get_possible_types s t0)%SEQ) :
          forall ptys, uniq ptys ->
                  t \in ptys ->
                        t ⊢ [seq InlineFragment sty (ground s sty β) | sty <- ptys] ≡ ground s t β.
        elim=> //= pty ptys IHptys /andP [Hnin Huniq].
        rewrite inE => /orP [/eqP Hteq | Htin].
        rewrite -Hteq.
        apply: EIF11.
        admit. (* t <: t *)
        rewrite -[X in _ ⊢ _ ≡ X]cats0.
        apply: equiv_cat_tail.
        admit. (* all t' ≠ t -> frags evaluate to nothing *)
        have Hfapplies : (does_fragment_type_apply s t pty) = false by admit.
        by apply: EIF21 => //=; apply: IHptys.
        admit. (* uniqueness of intersection + t ∈ both subtypes *)
        
        apply: IH => //=; ssromega.
        apply: equiv_trans.
        apply: equiv_cat_hd; apply: IH => //=; [by ssromega| admit].
        exact: H0.

        
    (* Case EIF12 *)
    - apply: EIF12 => //=.
      apply: IH => //=.
      admit. (* Fail : Probably need to do induction over the sum of both lists' sizes ? *)

    (* Case : EIF21 *)
    - case Hscope: is_object_type => /=.
      (* ty ∈ Ot *)
      * have Hteq : t = ty by admit. (* Same object *)
        rewrite -Hteq H /=.
        apply: IH => //=; first by ssromega.
        admit. (* t <: t *)

      (* ty ∈ At *)
      * case Ht : is_object_type => //=.
        + case Hfapplies : does_fragment_type_apply => /=; last by apply: IH => //=; ssromega.
          by apply: EIF21 => //=; apply: IH => //=; ssromega.
        + apply: equiv_trans.
          apply: (equiv_cat_hd t _ [::]).
          admit. (* t ∈ subtypes of t but not ∉ subtypes of t0 -> not in the intersection *)
          by rewrite cat0s; apply: IH => //=; ssromega.
        
    - apply: EIF22 => //=.
      apply: IH => //=.
      admit. (* Fail *)

  Admitted.

  Lemma filter_frag_queries_swap t f (φ : seq (@Query Name Vals)) :
    filter_queries_with_label f (filter_fragments_with_guard t φ) =
    filter_fragments_with_guard t (filter_queries_with_label f φ).
  Proof.
  Admitted.
    
  Lemma filter_invalid_frag_is_equiv ty t φ :
    does_fragment_type_apply s t ty ->
    ty ⊢ filter_fragments_with_guard t φ ≡ φ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty φ => //= [| n IH] ty φ.
    - by rewrite leqn0 => /queries_size_0_nil ->; simp filter_fragments_with_guard; constructor.
    - case: φ => //=; case=> [f α | | f α β | | t' β] φ; simp query_size => /= Hleq; simp filter_fragments_with_guard.

    - constructor.
      rewrite filter_frag_queries_swap; apply: IH => //=.
      by have Hfleq := (filter_queries_with_label_leq_size f φ); ssromega.

    - admit.

    - move=> Happlies; case Hlook : (lookup_field_in_type s ty f) => [fld|] /=.

      * apply: ENF1; first exact: Hlook.
        move=> t' Hin.
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
      
      * apply: ENF1 => //=; first exact: Hlook.
        + move=> t' Htin.
          rewrite -filter_remove_swap.
          have -> : find_queries_with_label s f t (filter_queries_with_label f (remove_redundancies φ)) = [::] by admit.
          simp merge_selection_sets => /=.
          rewrite cats0.
          have -> : find_fields_with_response_name Name Vals f φ = find_queries_with_label s f t φ by admit.
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

      
  Theorem equiv_eval ty u φ φ' :
    ty ⊢ φ ~ φ'  ->
    ⟦ φ ⟧ˢ in u = ⟦ φ' ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty u φ φ' => //= [| n IH] ty u φ φ'.
    - rewrite leqn0 => /queries_size_0_nil ->. admit.
    - move=> Hleq Heq.
      case: Heq Hleq => //=.

    - move=> f α fld φ1 φ2 Hlook Hfeq; simp query_size => Hleq.
      simp execute_selection_set; rewrite Hlook /=.
      case (u.(fields) _) => /= [[v | vs] |]; congr cons;
      apply: (IH ty) => //=;
      have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
 
    - move=> f α φ1 φ2 Hlook *; simp execute_selection_set; rewrite Hlook /=.
      by apply: (IH ty) => //=.


    - move=> f α β χ fld φ1 φ2 Hlook Hseq Hfeq; simp query_size => Hleq.
      simp execute_selection_set; rewrite Hlook /=.
      case fld.(return_type) => rty /=.
      * case ohead => [v |] /=;
        congr cons; last by apply: (IH ty) => //=; have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
        congr pair; congr Object.
        apply: (IH u.(type) v) => //=.
        rewrite queries_size_app.
         have Hleq1 := (found_queries_leq_size s f u.(type) φ1).
         have Hleq2 := (merged_selections_leq (find_queries_with_label s f u.(type) φ1)); ssromega.

         apply: (IH ty) => //=.
           by have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.

      *  congr cons;  last by apply: (IH ty) => //=; have Hfleq := (filter_queries_with_label_leq_size f φ1); ssromega.
         congr pair; congr Array; apply/eq_in_map=> v Hin.
         congr Object; apply: (IH u.(type) v) => //=.
          rewrite queries_size_app.
         have Hleq1 := (found_queries_leq_size s f u.(type) φ1).
         have Hleq2 := (merged_selections_leq (find_queries_with_label s f u.(type) φ1)); ssromega.

      * move=> f α β χ φ1 φ2 Hlook Heq; simp query_size => Hleq; simp execute_selection_set; rewrite Hlook /=.
        apply: (IH ty) => //=; ssromega.

    - move=> t β φ1 φ2 Happl Heq; simp query_size => Hleq; simp execute_selection_set; rewrite Happl /=.
      apply: (IH ty) => //=; rewrite queries_size_app; ssromega.

    - move=> t β φ1 φ2 Hnappl Heq; simp query_size => Hleq; simp execute_selection_set; rewrite Hnappl /=.
      apply: (IH ty) => //=; ssromega.
  Admitted.

 

  Lemma empty_frags_equiv_nil ty u pty :
    ty ⊢ [seq InlineFragment t [::] | t <- pty] ~ [::] in u.
  Proof.
    elim: pty => //= [| t pty IH]; first by constructor.
    case Hfappl: (does_fragment_type_apply s u.(type) t) => /=.
    apply: EIF1 => //=.
    by apply: EIF2.
  Qed.

    
  Lemma inlining_equiv ty u pty f α :
    ty ⊢ [seq InlineFragment t [:: SingleField f α] | t <- pty]  ~ 
       [:: SingleField f α] in u.
  Proof.
    elim: pty => //= [| t pty IH].
    - admit.
    - case Happl: (does_fragment_type_apply s u.(type) t).

      * apply: EIF1 => //=.
        case Hlook : (lookup_field_in_type s u.(type) f) => [fld |] /=.
        apply: ESF1; first exact: Hlook.
        have /(_ pty) -> : forall qs, filter_queries_with_label f [seq InlineFragment t0 [:: SingleField f α] | t0 <- qs] =
               [seq InlineFragment t0 [::] | t0 <- qs].
        elim=> //= q qs IHqs; simp filter_queries_with_label => /=; case: eqP => //= _; simp filter_queries_with_label.
        by rewrite IHqs.

        simp filter_queries_with_label; apply: empty_frags_equiv_nil.

        apply: ESF2 => //=.
        admit.

      * apply: EIF2 => //=.
  Admitted.
        
        
                                  
  Lemma grounding_is_equiv ty u φ :
    ty ⊢ ground s ty φ ~ φ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty u φ => //= [| n IH] ty u φ.
    - rewrite leqn0 => /queries_size_0_nil ->; simp ground; constructor.
    - case: φ => [| q qs]; first by intros; simp ground; constructor.
      case: q => [f α | | f α φ | | t φ]; simp query_size.

    - move=> Hleq; simp ground.
      case Hscope : is_object_type => /=.
      case Hlook : (lookup_field_in_type s u.(type) f) => [fld|] /=.
      apply: (ESF1 ty u f α fld) => //=.
      admit.
      apply: ESF2 => //=.
      by apply: IH.

    - simp try_inline_query; case: eqP => //= Hpty.
      admit.
      admit.

    - admit.

    - move=> Hleq; simp ground; case Hlook : lookup_field_in_type => [fld |] /=.
      case Hscope : is_object_type => /=.
      case Hlook2 : (lookup_field_in_type s u.(type) f) => [ufld |] /=.
      apply: ENF1; first exact Hlook2.
      move=> v.
      
      
      
      
      
      
  Lemma find_filtered_neq_eq ty f f' qs :
    f' <> f ->
    find_queries_with_label s f' ty (filter_queries_with_label f qs) =
    find_queries_with_label s f' ty qs.
  Proof.
    funelim (filter_queries_with_label f qs) => //= Hneq; rewrite /find_queries_with_label; simp ble => //=.
    - case does_fragment_type_apply => //=;
      rewrite -?/(find_queries_with_label s f' ty _);
                                        rewrite ?H // ?H0 //.
  Admitted.

  
  Lemma equiv_filter ty f φ φ' :
    ty ⊢ φ ~ φ' ->
    ty ⊢ filter_queries_with_label f φ ~ filter_queries_with_label f φ'.
  Proof.
    elim=> //= [| f' α qs1 qs2 Heq Hfeq]; simp filter_queries_with_label => /=.
    - constructor.
    - by case: eqP => //= _; constructor.
    - (* move=> ty' uty f' α β χ fdef qs1 qs2 Heq Hfeq Hlook Hsbeq Hfsbeq.
      simp filter_queries_with_label => /=; case: eqP => //= Hneq.
      eapply ENF => //=.
      apply: Hlook.
      rewrite !find_filtered_neq_eq //.

    - move=> ty' f' α β χ qs1 qs2 Heq Hfeq Hlook.
      simp filter_queries_with_label => /=; case: eqP => //= _.
      by constructor.
  Qed.*)
  Admitted.

 
  Lemma equiv_cat_hd ty qs1 qs2 qs :
    ty ⊢ qs1 ~ qs2 ->
    ty ⊢ qs1 ++ qs ~ qs2 ++ qs.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size qs1)) => n.
    elim: n qs qs1 qs2 ty => //= [| n IH] qs qs1 qs2 ty.
    admit.

    case: qs1 => /= [| q qs1 ] Hleq Heq.
    by inversion Heq; rewrite cat0s; apply: equiv_refl.

    move: Hleq; inversion Heq; simp query_size => Hleq; rewrite cat_cons.
    
    - by constructor; apply: IH.
    
    - by constructor; apply: IH.
      
    - apply: ENF => //.
      apply: IH => //=. admit. (* ssromega. *)
      exact: H3.
      rewrite 2!find_queries_with_label_cat 2!merge_selection_sets_cat.
      rewrite 2!catA.
      apply: IH => //.
      rewrite queries_size_app.
      have Hleq1 := (found_queries_leq_size s f ty qs1).
      have Hleq2 := (merged_selections_leq (find_queries_with_label s f ty qs1)).
      ssromega.

    - constructor => //; apply: IH => //. admit.
  Admitted.

   Lemma equiv_cat_tail ty qs1 qs2 qs :
    ty ⊢ qs1 ~ qs2 ->
    ty ⊢ qs ++ qs1 ~ qs ++ qs2.
  Proof.
  Admitted.

  Lemma equiv_cat ty qs1 qs1' qs2 qs2' :
    ty ⊢ qs1 ~ qs1' ->
    ty ⊢ qs2 ~ qs2' ->
    ty ⊢ qs1 ++ qs2 ~ qs1' ++ qs2'.
  Proof.
  Admitted.


  Lemma ground_preserves_equiv ty φ :
    ty ⊢ ground s ty φ ~ φ.
  Proof.
    elim: φ => //= [| q φ IH]; simp ground; first by constructor.

    case: q; intros; simp ground.

    - case is_object_type => //=.
      * by constructor.
      * simp try_inline_query; case: eqP => //= Hpty; first by constructor.
        rewrite -[SingleField _ _ :: φ]cat1s.
        apply: equiv_cat => //.
  Admitted.
  
    
  Lemma equiv_ble ty u φ φ' :
    ty ⊢ φ ~ φ' ->
    ⟦ φ ⟧ˢ in u = ⟦ φ' ⟧ˢ in u.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n ty u φ φ' => //= [| n IH] ty u φ φ'.
    - admit. 
    - case: φ => //= [| q φ] Hleq Heq; first by inversion Heq.

      case:  q Heq Hleq; intros.

      * inversion Heq.
        simp execute_selection_set; case Hlook : lookup_field_in_type => [fld|] //=.
        case (u.(fields) _) => [[v | vs] |] /=; congr cons; apply: IH; do ? by apply: (equiv_filter ty).
        admit.
        admit.
        admit.
        apply: (IH ty) => //.

      * admit.

      * simp query_size in Hleq.
        inversion Heq.
        simp execute_selection_set => //=.
        case Hlook: lookup_field_in_type => [fld|] /=; last apply: (IH ty) => //=.
        case fld.(return_type) => rty /=.
        case ohead => [v |] //=.
        congr cons.
        congr pair; congr Object.
        apply: IH => //=.
        admit.

  Admitted.

  Lemma ground_preserves_semantics ty u φ :
    ⟦ ground s ty φ ⟧ˢ in u = ⟦ φ ⟧ˢ in u.
  Proof.
    apply: equiv_ble.
    apply: ground_preserves_equiv.
  Qed.

        
        

  Inductive BaseRewrite (ty : NamedType) : seq Query -> seq (@Query Name Vals) -> Prop :=
  | SF : forall f α qs,
      BaseRewrite ty (SingleField f α :: qs ++ [:: SingleField f α]) (SingleField f α :: qs)

  | NF : forall f α φ β qs,
      find_queries_with_label s f ty qs = [::] ->
      BaseRewrite ty (NestedField f α φ :: qs ++ [:: NestedField f α β]) (NestedField f α (φ ++ β) :: qs)


  (* | IF_Spread : forall t φ1 φ,
      BaseRewrite ty [:: InlineFragment t (φ1 :: φ)] [:: InlineFragment t [:: φ1]; InlineFragment t φ] *)

  (* | IF_Wrap : forall qs,
      BaseRewrite ty qs [:: InlineFragment ty qs] *)

  | IF_Wrap : forall q1 qs,
      BaseRewrite ty (q1 :: qs) (InlineFragment ty [:: q1] :: q1 :: qs) (* Unnecessary I think? *)
                  
  | IF_Absorb : forall t φ qs,
      BaseRewrite ty (InlineFragment t [:: InlineFragment t φ] :: qs)
                  (InlineFragment t φ :: qs)

  | IF_Int : forall t to q1 qs,
      to \in implementation s t ->
             BaseRewrite ty (q1 :: qs) (InlineFragment to [:: q1] :: q1 :: qs)

  | IF_Union : forall t to φ,
      to \in union_members s t ->
             BaseRewrite ty [:: InlineFragment t φ] [:: InlineFragment to φ]

  | IF_Del : forall t1 t2 φ,
      is_object_type s t1 ->
      is_object_type s t2 ->
      t1 <> t2 ->
      BaseRewrite ty [:: InlineFragment t1 [:: InlineFragment t2 φ]] [::].


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
     by rewrite queries_size_app; ssromega.
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
        rewrite 2!catA; apply: IH => //; rewrite queries_size_app; ssromega.
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
          rewrite Hinpty2 Hfapplies /= -ground_cat; apply: IH => //; by rewrite queries_size_app; rewrite -/(queries_size φ) in Hleq; ssromega.
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
   all: do [by rewrite ?queries_size_app -/(queries_size φ); ssromega].
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
