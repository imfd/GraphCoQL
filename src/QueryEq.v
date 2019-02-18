Require Import List Relations.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
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

Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.
Require Import QueryConformance.
Require Import QuerySemantic.
Require Import NRGTNF.

Require Import String.

Section Eq.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Inductive Correct schema : (NamedType * NamedType) -> Query -> Prop :=
  | CF : forall f α root current,
      query_conforms schema current (SingleField f α) ->
      Correct schema (root, current) (SingleField f α)

  | CLF : forall l f α root current,
      query_conforms schema current (LabeledField l f α) ->
      Correct schema (root, current) (LabeledField l f α)
               
  | CNF : forall f α ϕ root current ty',
      query_conforms schema current (NestedField f α ϕ) ->
      lookup_field_type schema current f = Some ty' ->
      Forall (Correct schema (name_of_type ty', name_of_type ty')) ϕ ->
      Correct schema (root, current) (NestedField f α ϕ) 
               
  | CNLF : forall l f α ϕ root current ty',
      query_conforms schema current (NestedLabeledField l f α ϕ) ->
      lookup_field_type schema current f = Some ty' ->
      Forall (Correct schema (name_of_type ty', name_of_type ty')) ϕ ->
      Correct schema (root, current) (NestedLabeledField l f α ϕ) 

  (* If the query conforms to a type in scope, which is the same as the
     root type, then anything is correct as the inline's guard 
     (the conformance check rules out anything weird)
   *)
  | CIF_Any : forall root t ϕ,
      query_conforms schema root (InlineFragment t ϕ) ->
      Forall (Correct schema (root, t)) ϕ ->
      Correct schema (root, root) (InlineFragment t ϕ)

  | CIF_Root : forall root current ϕ,
      query_conforms schema current (InlineFragment root ϕ) ->
      Forall (Correct schema (root, root)) ϕ ->
      Correct schema (root, current) (InlineFragment root ϕ)

  (* The inline's guard is the same as the previous one *)            
  | CIF_Current : forall root current ϕ,
      (root \in get_possible_types schema current \/ current \in get_possible_types schema root) ->
      query_conforms schema current (InlineFragment current ϕ) ->
      Forall (Correct schema (root, current)) ϕ ->
      Correct schema (root, current) (InlineFragment current ϕ).


  Lemma correct_object_E schema root current t ϕ :
    is_object_type schema t ->
    Correct schema (root, current) (InlineFragment t ϕ) ->
    (is_subtype schema (NT t) (NT current)).
      (*
    (t = root /\ is_subtype schema (NT t) (NT current)) |
    (t = current /\ is_subtype schema (NT t) (NT root))]. *)
  Proof.
    move=> Hobj Hok.
    inversion Hok.
    - move: H2; rewrite /query_conforms.
      move/and4P=> [_ Hspread _ _].
      move: (object_spreads_E Hobj Hspread) => [-> | Himpl | Hmb]; rewrite /is_subtype; apply/or3P.
        by constructor 1; apply/eqP.
        by constructor 2; rewrite declares_in_implementation.
        by constructor 3.
    - move: H2; rewrite /query_conforms.
      move/and4P=> [_ Hspread _ _].
      move: (object_spreads_E Hobj Hspread) => [-> | Himpl | Hmb]; rewrite /is_subtype;
      apply/or3P.                                        
        by constructor 1; apply/eqP.
        by constructor 2; rewrite declares_in_implementation.
        by constructor 3.
    - by rewrite /is_subtype; apply/or3P; constructor 1; apply/eqP.
  Qed.

  Lemma correct_conforms schema root current q :
    Correct schema (root, current) q ->
    query_conforms schema current q.
  Proof. by move=> H; inversion H. Qed.

  Lemma queries_correct_conform schema root current queries :
    Forall (Correct schema (root, current)) queries ->
    all (query_conforms schema current) queries.
  Proof.
    elim: queries => // hd tl IH.
    move=> H; inversion H => //=.
    apply/andP; split.
    apply: (correct_conforms H2).
    by apply: IH.
  Qed.

    
  Definition QueryEq schema (g : @conformedGraph N Name Vals schema) u ty (q1 q2 : Query)  :=
    query_conforms schema ty q1 ->
    query_conforms schema ty q2 ->
    eval schema g u q1 = eval schema g u q2.

  Definition QueriesEq schema (g : @conformedGraph N Name Vals schema) u ty (q1 q2 : seq Query) :=
    queries_conform schema ty q1 ->
    queries_conform schema ty q2 ->
    eval_queries schema g u q1 = eval_queries schema g u q2.
    

  Lemma inline_nested_empty schema (g : @conformedGraph N Name Vals schema) :
    forall t1 t2 ϕ,
      is_object_type schema t1 ->
      is_object_type schema t2 ->
      t1 <> t2 ->
      eval schema g g.(root) (InlineFragment t1 [:: (InlineFragment t2 ϕ)]) = [::].
  Proof.
    move=> t1 t2 ϕ.
    funelim (is_object_type schema t1) => //.
    funelim (is_object_type schema0 t2) => //.
    move=> _ _ Hdiff.
    rewrite eval_equation_5 Heq0.
    case: eqP => //= <-.
    rewrite Heq.
    by case: eqP => // Ht1t2; rewrite Ht1t2 in Hdiff.
  Qed.

  Lemma inline_query_preserves schema (g : @conformedGraph N Name Vals schema):
    forall ϕ u,
      u \in nodes g.(graph) ->
      eval schema g u ϕ = eval schema g u (InlineFragment u.(type) [:: ϕ]).
  Proof.
    move=> ϕ u Hin; case: g Hin.
    move=> g Hr He Hf Hn /= Hin.
    rewrite /nodes_have_object_type in Hn.
    move/seq.allP /(_ u Hin): Hn.
    case: u Hin => id ty flds Hin. rewrite /type. funelim (is_object_type schema ty) => //.
    move=> _.
    rewrite Heq.
    case: ϕ.
    move=> name α. rewrite /eval. 
    simpl.  Admitted.

  Lemma interface_N_obj schema ty :
    is_interface_type schema ty -> ~~(is_object_type schema ty).
  Proof. rewrite /is_interface_type.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => //.
    rewrite /is_object_type.
      by move=> i flds Hlook; rewrite Hlook.
  Qed.

  Lemma inline_preserves_conformance schema type_in_scope ϕ :
    query_conforms schema type_in_scope ϕ ->
    query_conforms schema type_in_scope (InlineFragment type_in_scope [:: ϕ]).
  Proof.
    rewrite {2}/query_conforms.
    move=> Hqc.
    apply/and4P; split=> //.
    apply/or3P. apply: (type_in_scope_N_scalar_enum Hqc).
    rewrite /is_fragment_spread_possible /get_possible_types.
    
    move: (type_in_scope_N_scalar_enum Hqc) => [Hobj | Hint | Hunion].
    funelim (is_object_type schema type_in_scope) => //.
    Admitted.
 
  
  Lemma filter_preserves_pred T (p pred : T -> bool) (s : seq T) :
    all p s ->
    all p [seq x <- s | pred x].
  Proof.
    elim: s => [//| x s' IH] /=.
    move/andP=> [Hpx Hall].
    case (pred x) => //=.
      by move/IH: Hall => Hall; apply/andP.
      by apply: IH.
  Qed.

  
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
  
  Inductive QueryRed (schema : @wfSchema Name Vals) (type_in_scope : NamedType) : seq Query -> seq Query -> Prop :=

  | SQ : forall ϕ ϕ',
      query_conforms schema type_in_scope ϕ ->
      multi (AtomicQueryRed schema type_in_scope) ϕ ϕ' ->
      QueryRed schema type_in_scope [:: ϕ] [:: ϕ']
               
  | SS1 : forall ϕ ϕ' ϕs ϕs',
      query_conforms schema type_in_scope ϕ ->
      all (query_conforms schema type_in_scope) ϕs ->
      multi (AtomicQueryRed schema type_in_scope) ϕ ϕ' ->
      multi (QueryRed schema type_in_scope) ϕs ϕs' -> 
      QueryRed schema type_in_scope (ϕ :: ϕs) (ϕ' :: ϕs')
                   
  | SF_None : forall (ϕ : seq (@Query Name Vals)) f α,
      let ϕ' := filter (fun q => ~~(partial_query_eq (SingleField f α) q)) ϕ in
      query_conforms schema type_in_scope (SingleField f α) ->
      all (query_conforms schema type_in_scope) ϕ ->
      QueryRed schema type_in_scope ((SingleField f α) :: ϕ) ((SingleField f α) :: ϕ')

  | LF_Some : forall (ϕ : seq (@Query Name Vals)) l f α,
      let ϕ' := filter (fun q => ~~(partial_query_eq (LabeledField l f α) q)) ϕ in
      query_conforms schema type_in_scope (LabeledField l f α) ->
      all (query_conforms schema type_in_scope) ϕ ->
      QueryRed schema type_in_scope ((LabeledField l f α) :: ϕ) ((LabeledField l f α) :: ϕ')

  | NF_Some : forall (ϕ β : seq (@Query Name Vals)) (f : Name) (α α' : {fmap Name -> Vals}),
      let subqueries := foldr (fun q acc => if q is NestedField f' α' χ then
                                          if (f' == f) && (α == α') then
                                            χ ++ acc
                                          else
                                            acc
                                        else
                                          acc) [::] ϕ
      in
      let ϕ' := (filter (fun q => ~~(partial_query_eq (NestedField f α β) q)) ϕ) in
      query_conforms schema type_in_scope (NestedField f α β) ->
      all (query_conforms schema type_in_scope) ϕ ->
      QueryRed schema type_in_scope
               ((NestedField f α β) :: ϕ)
               ((NestedField f α (β ++ subqueries)) :: ϕ')
               
                
  | Inline_spread : forall t ϕ ϕ' ϕs,
      query_conforms schema type_in_scope (InlineFragment t  (ϕ :: ϕ')) ->
      all (query_conforms schema type_in_scope) ϕs ->
      QueryRed schema type_in_scope ((InlineFragment t  (ϕ :: ϕ')) :: ϕs)
                      ((InlineFragment t [:: ϕ]) :: (InlineFragment t ϕ') :: ϕs)

  | Inline_same : forall ϕ,
      query_conforms schema type_in_scope (InlineFragment type_in_scope ϕ) ->
      QueryRed schema type_in_scope [:: InlineFragment type_in_scope ϕ] ϕ
               

  with
  AtomicQueryRed (schema : @wfSchema Name Vals) (type_in_scope : NamedType) : Query -> Query -> Prop :=
  | AQR_Refl : forall ϕ,
      AtomicQueryRed schema type_in_scope ϕ ϕ
                     
  | AQR_Nested : forall f α ϕ ϕ' ty',
      query_conforms schema type_in_scope (NestedField f α ϕ) ->
      lookup_field_type schema type_in_scope f = Some ty' ->
      multi (QueryRed schema ty') ϕ ϕ' ->
      AtomicQueryRed schema type_in_scope (NestedField f α ϕ) (NestedField f α ϕ')

  | AQR_LabeledNested : forall l f α ϕ ϕ' ty',
      query_conforms schema type_in_scope (NestedLabeledField l f α ϕ) ->
      lookup_field_type schema type_in_scope f = Some ty' ->
      multi (QueryRed schema ty') ϕ ϕ' ->
      AtomicQueryRed schema type_in_scope (NestedLabeledField l f α ϕ) (NestedLabeledField l f α ϕ')

  | AQR_Inline_Wrap : forall ϕ,
      query_conforms schema type_in_scope ϕ ->
      AtomicQueryRed schema type_in_scope ϕ (InlineFragment type_in_scope [:: ϕ])
                     
  | AQR_Inline : forall t ϕ ϕ',
      query_conforms schema type_in_scope (InlineFragment t ϕ) ->
      multi (QueryRed schema t) ϕ ϕ' ->
      AtomicQueryRed schema type_in_scope (InlineFragment t ϕ) (InlineFragment t ϕ')

  | AQR_Inline_nested : forall t ϕ,
      query_conforms schema type_in_scope (InlineFragment t [:: InlineFragment t ϕ]) ->
      AtomicQueryRed schema type_in_scope (InlineFragment t [:: InlineFragment t ϕ]) (InlineFragment t ϕ) 

  | AQR_Inline_Int : forall t ti ϕ,
      query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
      t \in implementation schema ti ->
            AtomicQueryRed schema type_in_scope (InlineFragment ti ϕ) (InlineFragment t ϕ)
                           
  | AQR_Inline_Impl : forall ti ϕ,
      query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
      Forall (Correct schema (type_in_scope, type_in_scope)) ϕ ->
      type_in_scope \in implementation schema ti ->
             AtomicQueryRed schema type_in_scope (InlineFragment ti ϕ) (InlineFragment type_in_scope ϕ)
                                              
  .


  Lemma asf schema (g : @conformedGraph N Name Vals schema)  u type_in_scope ti ϕ :
     query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
     type_in_scope \in implementation schema ti ->
            eval schema g u (InlineFragment ti ϕ) = eval schema g u (InlineFragment type_in_scope ϕ). 
  Proof.
    move=> Hqc Himpl.
    move: (has_implementation_is_interface Himpl) => Hint.
    rewrite !eval_equation_5.
    funelim (is_interface_type schema ti) => //.
    rewrite Heq.
    move: (in_implementation_is_object Himpl) => /is_object_type_E [obj [intfs [flds Hlook]]].
    rewrite Hlook.
    case: ifP => //.
    rewrite declares_in_implementation.
  Abort.
  (* Missing info on node -> type of node should be same as the one in scope *)
    
  
  (*Lemma AQR_SFE schema ty ϕ n α : AtomicQueryRed schema ty (SingleField n α) ϕ ->
                               ϕ = SingleField n α.
  Proof. by move=> H; inversion H. Qed.

  *)


  Lemma filter_all_predC1 (T : eqType) (s : seq T) (x : T) :
    [seq x' <- s | predC1 x x'] = [::] ->
    forall x', x' \in s -> x' = x.
    elim: s x => [//| n s' IH] x /=.
    case: ifP => //.
    case: eqP => // -> _ /IH H.
    by move=> x'; rewrite in_cons => /orP [/eqP ->|]; [|apply: H]. 
  Qed.



  Lemma queries_conform_cons schema ty hd tl :
    queries_conform schema ty (hd :: tl) -> query_conforms schema ty hd.
  Proof.
    rewrite /queries_conform.
      by move/andP=> [_ /= /andP [Hhd _]].
  Qed.


  Lemma nested_conforms_list schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) -> ϕ != [::].
  Proof.
    rewrite /query_conforms.
    case lookup_field_in_type => // f.
    case: ifP => // _.
    by move/and3P=> [Hne _ _].
  Qed.

  Lemma not_nil_spread {A : eqType} (lst : seq A) : lst != [] -> exists x lst', lst = x :: lst'.
  Proof.
      by case: lst => // x lst' H; exists x; exists lst'.  Qed.
  
  Lemma single_field_correct schema ty ty' n α :
    query_conforms schema ty' (SingleField n α) ->
    Correct schema (ty, ty') (SingleField n α).
  Proof. by move=> Hqc; apply: CF. Qed.

 


  Lemma nf_correct_lookup_some schema root current n α ϕ :
    Correct schema (root, current) (NestedField n α ϕ) ->
    exists fld, lookup_field_type schema current n = Some fld. 
  Proof.
    move=> H; inversion H.
      by exists ty'.
  Qed.

  Lemma nlf_correct_lookup_some schema root current l n α ϕ :
    Correct schema (root, current) (NestedLabeledField l n α ϕ) ->
    exists fld, lookup_field_type schema current n = Some fld. 
  Proof.
    move=> H; inversion H.
      by exists ty'.
  Qed.

  Lemma nf_queries_conform'' schema ty n α ϕ fld :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedField n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    move=> Hlook; rewrite /query_conforms.
    rewrite Hlook.
    case: ifP => // _; rewrite -/(query_conforms schema fld.(return_type)).
    move/and3P=> [HNnil Hargs Hall].
    rewrite /queries_conform.
    by apply/andP. 
  Qed.

  Lemma nlf_queries_conform'' schema ty l n α ϕ fld :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedLabeledField l n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    move=> Hlook; rewrite /query_conforms.
    rewrite Hlook.
    case: ifP => // _; rewrite -/(query_conforms schema fld.(return_type)).
    move/and3P=> [HNnil Hargs Hall].
    rewrite /queries_conform.
    by apply/andP. 
  Qed.
    
    
  Lemma lookup_field_or_type schema lookup_type ty name fld :
    lookup_field_in_type schema lookup_type name = Some fld ->
    lookup_field_type schema lookup_type name = Some ty ->
    ty = fld.(return_type).
  Proof.
    by rewrite /lookup_field_type; move=> ->; case. Qed.

  
  (**
     If query is free of issues and its type in the schema is "ty",
     then its subqueries are also free of issues for the given type.
   **)
  Lemma nested_field_subqueries_correct schema root current n α ϕ ty :
    Correct schema (root, current) (NestedField n α ϕ) ->
    lookup_field_type schema current n = Some ty ->
    Forall (Correct schema (name_of_type ty, name_of_type ty)) ϕ.
  Proof.  by move=> H Hlook; inversion H; rewrite Hlook in H6; case: H6 => ->. Qed.

  Lemma nlf_queries_correct schema root current l n α ϕ fld :
    lookup_field_type schema current n = Some fld ->
    Correct schema (root, current) (NestedLabeledField l n α ϕ) ->
    Forall (Correct schema (name_of_type fld, name_of_type fld)) ϕ.
  Proof.  by move=> Hlook H; inversion H; rewrite Hlook in H7; case: H7 => ->. Qed.
  

  Lemma nf_queries_eq schema (g : @conformedGraph N Name Vals schema) u n α ϕ ϕ' :
    (forall v, eval_queries schema g v ϕ = eval_queries schema g v ϕ') ->
    eval schema g u (NestedField n α ϕ) = eval schema g u (NestedField n α ϕ').
  Proof.
    move=> Hqs.
    do 2 rewrite eval_equation_3.
    case lookup_field_type => //.
    case=> [nt | lt].
    case get_target_nodes_with_field => // v1 vn /=.
    by move: (Hqs v1) => ->. 
    case get_target_nodes_with_field => // v1 vn /=.
    move: (Hqs v1) => ->.
  Admitted.

  
  
  Lemma u_and_target_nodes_in_nodes (g : @graphQLGraph N Name Vals) u fld :
    u \in nodes g -> all (fun v => v \in nodes g) (get_target_nodes_with_field g u fld).
  Proof.
  Admitted.

  Lemma ohead_in (A : eqType) (lst : seq A) (v : A) :
    ohead lst = Some v ->
    v \in lst.
  Proof.
    elim: lst => // x lst' IH /=.
      by case=> ->; rewrite inE; apply/orP; left.
  Qed.
    
  Lemma ohead_in_nodes (g : @graphQLGraph N Name Vals) nds v :
    all (fun node => node \in nodes g) nds ->
    ohead nds = Some v ->
    v \in nodes g. 
  Proof.
    elim: nds => // x nds IH /=.
    by move=> H; case=> Heq; rewrite Heq in H; move/andP: H => [H _]. 
  Qed.

  Lemma ohead_cons (A : eqType) H (x : A) lst :
    ohead (x :: lst) = H -> Some x = H.
  Proof. done. Qed.

  Lemma map_fs {A B C : eqType} (lst : seq A) (f : A -> B -> C) (x y : B):
    (forall u,
      u \in lst ->
            f u x = f u y) ->
      [seq f v x | v <- lst] = [seq f v y | v <- lst].
  Proof.
    elim: lst => // hd lst' IH.
    move=> H /=. 
    move: (H hd). rewrite inE. case eqP => // _.
    move/(_ (orTb (hd \in lst'))) => Hf. rewrite Hf.
    congr cons.
    move: H.
    Admitted.

  Lemma singleton (A : Type) (x y : A) : x = y -> [:: x] = [:: y]. Proof. by move=> ->. Qed.

  Lemma nrl_subqueries (n : Name) (ϕ ϕ' : seq (seq (@ResponseObject Name Vals))) : ϕ = ϕ' -> NestedListResult n ϕ = NestedListResult n ϕ'. Proof. by move=> ->. Qed.


 

  Lemma qwe schema (g : @conformedGraph N Name Vals schema) u qs qs' α n :
    (forall u : node_eqType N Name Vals, u \in nodes g -> eval_queries schema g u qs = eval_queries schema g u qs') ->
    [seq (eval_queries schema g v qs) | v <- get_target_nodes_with_field g u {| label := n; args := α |}] =
  [seq (eval_queries schema g v qs') | v <- get_target_nodes_with_field g u {| label := n; args := α |}].
  Proof. Admitted.

  Lemma inline_subqueries_conform schema ty t ϕ :
    query_conforms schema ty (InlineFragment t ϕ) ->
    queries_conform schema t ϕ.
  Proof.
    rewrite /query_conforms.
    move/and4P=> [_ _ Hne H].
    by rewrite /queries_conform; apply/andP. 
  Qed.

  Lemma inline_subqueries_correct schema root current t ϕ :
    Correct schema (root, current) (InlineFragment t ϕ) ->
    Forall (Correct schema (root, t)) ϕ.
  Proof.
      by move=> H; inversion H. Qed.

  Lemma no_repeated_filter (ϕ : @Query Name Vals) (ϕ' : seq Query) :
    ~~(has (partial_query_eq ϕ) (filter (fun q => ~~(partial_query_eq ϕ q)) ϕ')).
  Proof.
    elim: ϕ' => // q ϕ' IH.
    simpl.
    case: ifP => // Hnpeq.
    simpl.
    apply/orP.
    rewrite /not. move=> [Hpeq | Hhas].
    move: Hnpeq. rewrite /negb. case: ifP => //. rewrite Hpeq. done.
    move: IH; rewrite /negb. case: ifP=> //. rewrite Hhas. done.
  Qed.

  Lemma filter_preserves_non_repeated (ϕ : seq (@Query Name Vals)) p :
    no_repeated_query ϕ ->
    no_repeated_query (filter p ϕ).
  Proof.
  Admitted.

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

  Lemma queries_correct_impl schema ty ti queries :
    ty \in implementation schema ti ->
    Forall (Correct schema (ty, ti)) queries ->
    Forall (Correct schema (ty, ty)) queries.
  Admitted.

  Lemma ble schema ty ti queries :
    ty \in implementation schema ti ->
    query_conforms schema ty (InlineFragment ti queries) ->
    Correct schema (ty, ty) (InlineFragment ti queries) ->
    queries_conform schema ty queries.
  Admitted.

  Lemma bleble schema ty ti queries :
    ty \in implementation schema ti ->
    queries_conform schema ti queries ->
    Forall (Correct schema (ty, ti)) queries ->
    queries_conform schema ty queries.
  Admitted.

  Lemma foo schema ty ti queries :
    is_object_type schema ty ->
    is_interface_type schema ti ->
    is_fragment_spread_possible schema ty ti ->
    queries != [::] ->
    Forall (Correct schema (ty, ti)) queries ->
    query_conforms schema ty (InlineFragment ti queries).
  Proof.
    move=> Hobj Hint Hspread Hne Hqsok.
    rewrite /query_conforms.
    apply/and4P; split=> //.
      by apply/or3P; constructor 2.
    by move: (queries_correct_conform Hqsok).
  Qed.
  
  Lemma queries_conform_inv schema ty queries :
    queries != [::] ->
    all (query_conforms schema ty) queries ->
    queries_conform schema ty queries.
  Proof. by move=> *; rewrite /queries_conform; apply/andP. Qed.
  
  Theorem all_q_has_nrgtnf_q schema (g : @conformedGraph N Name Vals schema):
    forall (ϕ : @Query Name Vals),
      query_conforms schema schema.(query_type) ϕ ->
      Correct schema (schema.(query_type), schema.(query_type)) ϕ ->

      exists (ϕ' : seq (@Query Name Vals)),
        [/\ ϕ' != [::],
         Forall (Correct schema (schema.(query_type), schema.(query_type))) ϕ',
         are_in_normal_form schema ϕ',
         are_non_redundant ϕ',
         multi (QueryRed schema schema.(query_type)) [:: ϕ] ϕ' &
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
                     qs' != [::],
                     Forall (Correct schema (root, current)) qs',
                     are_in_normal_form schema qs',
                     are_non_redundant qs',
                     multi (QueryRed schema current) qs qs' &
                     forall u, u \in nodes g -> eval_queries schema g u qs = eval_queries schema g u qs']).

    - move=> f α; exists [:: (SingleField f α)]; split => //.
      by apply: Forall_cons.
      by apply: multi_refl.
    - move=> l f α; exists [:: (LabeledField l f α)]; split => //.
      by apply: Forall_cons.
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
      move: (IH ty' ty' Hqsc Hqsok) => {IH}; case=> qs' [Hqsne' Hqsok' Hqsnf' Hqsnr' Hred' Hev'].
      
      exists [:: (NestedField f α qs')]; split => //=.
      * apply: Forall_cons => //=.
        apply: CNF => //.
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
      move/and4P=> [/or3P [Hobj | Hint | Hunion] Hspread _ _].
      * move: (object_spreads_in_object_scope Hqobj Hobj Hqsc).
        case. move/(_ Hqc) => Heq _; rewrite -Heq.
        exists qs'; split=> //.
          by rewrite Heq; rewrite Heq in Hqsok'.
        apply: multi_step => //.
        rewrite -Heq in Hqc.
        apply: Inline_same => //.
        apply: Hred'.
        move: (Hev' g.(root) (root_in_nodes g)) => <-.
        rewrite Heq.
          by apply (eval_query_inline g qs).
      * exists qs'; split=> //; move: (interface_spreads_in_object_scope Hqobj Hint Hqc) => Himpl.
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
          apply: (queries_correct_impl Himpl Hqsok') => //.
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
          
          
      
      
  
        
End Eq.