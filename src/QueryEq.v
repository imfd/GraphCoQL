Require Import List.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


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

  | CIF_SS : forall t t' ϕ,  (* This includes the case when t = t' *)
      query_conforms schema t' (InlineFragment t ϕ) ->
      t \in get_possible_types schema t' ->
            Forall (Correct schema (t', t)) ϕ ->
            Correct schema (t', t') (InlineFragment t ϕ)   
                    
  | CIF_ST : forall t t' ϕ,
      query_conforms schema t (InlineFragment t ϕ) ->
      Forall (Correct schema (t', t)) ϕ ->
      Correct schema (t', t) (InlineFragment t ϕ)
                    
  | CIF_TT' : forall t t' ϕ,
      query_conforms schema t (InlineFragment t' ϕ) ->
      Forall (Correct schema (t, t')) ϕ ->
      Correct schema (t, t) (InlineFragment t' ϕ)
               
  | CIF_TS' : forall t t' ϕ,
      query_conforms schema t' (InlineFragment t' ϕ) ->
      Forall (Correct schema (t, t')) ϕ ->
      Correct schema (t, t') (InlineFragment t' ϕ)
               
  | CIF_TS : forall t t' ϕ,
      query_conforms schema t' (InlineFragment t ϕ) ->
      Forall (Correct schema (t, t)) ϕ ->
      Correct schema (t, t') (InlineFragment t ϕ).
  Set Elimination Schemes.

  

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
    rewrite /eval Heq0.
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

    


  Lemma filter_preserves T (p pred : T -> bool) (s : seq T) :
    seq.all p s ->
    seq.all p [seq x <- s | pred x].
  Proof.
    elim: s => [//| x s' IH] /=.
    move/andP=> [Hpx Hall].
    case (pred x) => //=.
      by move/IH: Hall => Hall; apply/andP.
      by apply: IH.
  Qed.

  
  Inductive QueryRed (schema : @wfSchema Name Vals) : seq Query -> seq Query -> Prop :=
  | SS1 : forall ϕ ϕ' ϕs,
      AtomicQueryRed schema ϕ ϕ' ->
      QueryRed schema [:: ϕ ; ϕs] [:: ϕ' ; ϕs]
                   
  | SF_None : forall (ϕ ϕ' : seq (@Query Name Vals)) n α,
      let ϕ' := filter (predC1 (SingleField n α)) ϕ in
      QueryRed schema ((SingleField n α) :: ϕ) ((SingleField n α) :: ϕ')

  | LF_Some : forall (ϕ ϕ' : seq (@Query Name Vals)) l n α,
      let ϕ' := filter (predC1 (LabeledField l n α)) ϕ in
      QueryRed schema ((LabeledField l n α) :: ϕ) ((LabeledField l n α) :: ϕ')

  | NF_Some : forall (ϕ ϕ' β : seq (@Query Name Vals)) (n : Name) (α α' : {fmap Name -> Vals}),
      let subqueries := foldr (fun q acc => if q is NestedField n' α' χ then
                                          if (n' == n) && (α == α') then
                                            χ ++ acc
                                          else
                                            acc
                                        else
                                          acc) [::] ϕ
      in
      let ϕ' := (filter (fun q => ~~(partial_query_eq (NestedField n α β) q)) ϕ) in 
      QueryRed schema ((NestedField n α β) :: ϕ)
                      ((NestedField n α (β ++ subqueries)) :: ϕ')
               
                
  | Inline_spread : forall t ϕ ϕ',
      QueryRed schema [:: (InlineFragment t  (ϕ :: ϕ'))]
                      [:: (InlineFragment t [:: ϕ]) ; (InlineFragment t ϕ')]
        

  with
  AtomicQueryRed (schema : @wfSchema Name Vals) : Query -> Query -> Prop :=
  | AQR_Refl : forall ϕ,
      AtomicQueryRed schema ϕ ϕ
                     
   | AQR_Nested : forall n α ϕ ϕ',
      QueryRed schema ϕ ϕ' ->
      AtomicQueryRed schema (NestedField n α ϕ) (NestedField n α ϕ')

  | AQR_LabeledNested : forall l n α ϕ ϕ',
      QueryRed schema ϕ ϕ' ->
      AtomicQueryRed schema (NestedLabeledField l n α ϕ) (NestedLabeledField l n α ϕ')
               
  | QR_Single_Inline : forall t ϕ ϕ',
      QueryRed schema ϕ ϕ' ->
      AtomicQueryRed schema (InlineFragment t ϕ) (InlineFragment t ϕ')

  | Inline_nested : forall t ϕ,
      AtomicQueryRed schema (InlineFragment t [:: InlineFragment t ϕ]) (InlineFragment t ϕ) 

  | AQR_Inline_Int : forall t t1 ϕ,
      t \in implementation schema t1 ->
            AtomicQueryRed schema (InlineFragment t1 ϕ) (InlineFragment t ϕ)

  | AQR_Inline_Union : forall t t1 ϕ,
      t \in union_members schema t1 ->
            AtomicQueryRed schema (InlineFragment t1 ϕ) (InlineFragment t ϕ)

                                              
  .

  Lemma AQR_SFE schema ϕ n α : AtomicQueryRed schema (SingleField n α) ϕ ->
                               ϕ = SingleField n α.
  Proof. by move=> H; inversion H. Qed.

  


  Lemma filter_all_predC1 (T : eqType) (s : seq T) (x : T) :
    [seq x' <- s | predC1 x x'] = [::] ->
    forall x', x' \in s -> x' = x.
    elim: s x => [//| n s' IH] x /=.
    case: ifP => //.
    case: eqP => // -> _ /IH H.
    by move=> x'; rewrite in_cons => /orP [/eqP ->|]; [|apply: H]. 
  Qed.


  (*
  Lemma query_filter_preserves (queries ϕ' : @QuerySet Name Vals) p pred :
    all pred queries -> filter p queries = Some ϕ' -> all pred ϕ'.
  Proof.
    move: ϕ'.
    elim queries using QuerySet_ind with (P0 := fun q => forall queries, all pred queries -> in_query q queries -> pred q).
    - move=> q H /= ϕ' Hq.
      case (p q).
      rewrite filter_helper_1_equation_1.
      case. move=> Heq; rewrite -Heq.
      rewrite all_equation_1. done.
      rewrite filter_helper_1_equation_2. done.
    - move=> q H q' H' ϕ'.
      rewrite all_equation_2. move/andP=> [Hq Hall].
      simpl. case Hfilt: (filter p q') => [sm|].
      case (p q).
      case. move=> Heq. rewrite -Heq.
      rewrite all_equation_2. apply/andP; split=> //.
      apply: H'. done. done. case. move=> <-. apply: H'. done. done. done.

    - by move=> n f q /allP H; apply: H.
    - by move=> l n f q /allP H; apply: H.
    - by move=> n f ϕ H q /allP H'; apply: H'.
    - by move=> l n f ϕ H q /allP H'; apply: H'.
    - by move=> t ϕ H q /allP H'; apply: H'.
  Qed. *)

  (*
  Lemma filter_preserves_normal (queries ϕ' : @QuerySet Name Vals) p :
    is_ground_typed_normal_form queries ->
    filter p queries = Some ϕ' ->
    is_ground_typed_normal_form ϕ'.
  Proof.
    move: ϕ'.
    elim queries using QuerySet_ind with (P0 := fun q => forall queries, is_ground_typed_normal_form queries ->
                                                                in_query q queries ->
                                                                is_query_in_normal_form q).
    - move=> q Hq ϕ' H /=.
       case (p q).
         * by rewrite filter_helper_1_equation_1; case=> <-.
         by rewrite filter_helper_1_equation_2.
    - move=> q Hq q' Hq' ϕ'.
      rewrite is_ground_typed_normal_form_equation_2; move/and3P=> [/orP [Hflds | Hins] Hnf Hnf'] /=;
      case Hfilt: (filter p q') => [sm|]; case (p q) => //; case=> <-.
      rewrite is_ground_typed_normal_form_equation_2.
      move: (Hq' sm Hnf' Hfilt).
  Admitted.
*)
(*
  Lemma filter_preserves_non_redundancy (queries ϕ' : @QuerySet Name Vals) p :
    is_non_redundant queries ->
    filter p queries = Some ϕ' ->
    is_non_redundant ϕ'.
  Proof.
    Admitted.
*)

  Lemma queries_conform_cons schema ty hd tl :
    queries_conform schema ty (hd :: tl) -> query_conforms schema ty hd.
  Proof.
    rewrite /queries_conform.
      by move/andP=> [_ /= /andP [Hhd _]].
  Qed.

  Lemma correct_conforms schema root current ϕ :
    Correct schema (root, current) ϕ ->
    query_conforms schema current ϕ.
  Proof.
    move: root current.
    elim ϕ using Query_ind with (Pl := fun qs => forall root current, qs != [::] -> Forall (Correct schema (root, current)) qs -> queries_conform schema current qs) => //.
    by intros; inversion H.
    by intros; inversion H.
    by move=> n α ϕ' IH root current H; inversion H.  
    by move=> l n α ϕ' IH root current H; inversion H.
    by move=> t ϕ' IH root current H; inversion H.
    move=> q IH qs IH' root current Hne H.
    rewrite /queries_conform.
    apply/andP; split => //.
    simpl. apply/andP; split => //.
    move: (Forall_cons_inv H) => [H1 H2].
    apply: (IH _ _ H1).
    case: qs IH' Hne H => //.
    move=> hd tl H.
    Admitted.

  Lemma nested_conforms_list schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) -> ϕ != [::].
  Proof.
    simpl.
    move/andP=> [/nilP H _]; case: eqP => //.
  Qed.

  Lemma not_nil_spread {A : eqType} (lst : seq A) : lst != [] -> exists x lst', lst = x :: lst'.
  Proof.
      by case: lst => // x lst' H; exists x; exists lst'.  Qed.
  
  Lemma single_field_correct schema ty ty' n α :
    Correct schema (ty, ty') (SingleField n α).
  Proof. apply: CF. Admitted.

 
   
  Lemma empty_queries_N_conform schema ty : ~ queries_conform schema ty [::].
  Proof. done. Qed.

  Lemma nf_queries_conform schema ty fld n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    lookup_field_in_type schema ty n = Some fld ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    rewrite /query_conforms.
    move/andP=> [/nilP HNnil Hlook].
    case H : lookup_field_in_type => [fld'|] //.
    case=> <-.
    rewrite H in Hlook. move/andP: Hlook => [Hargs Hall].
    rewrite -/(query_conforms schema fld') in Hall.
    rewrite /queries_conform.
    apply/andP. split.
    rewrite /negb. case eqP => //. done.
  Qed.

  Lemma nf_conforms_lookup_some schema ty  n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    exists fld, lookup_field_in_type schema ty n = Some fld.
  Proof. rewrite /query_conforms.
    move/andP=> [_].
    case Hlook : lookup_field_in_type => [fld'|] //.
    by exists fld'.
  Qed.

  Lemma nf_correct_lookup_some schema root current n α ϕ :
    Correct schema (root, current) (NestedField n α ϕ) ->
    exists fld, lookup_field_type schema current n = Some fld. 
  Proof.
    move=> H; inversion H.
      by exists ty'.
  Qed.
    
  Lemma nf_queries_conform' schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    exists ty', queries_conform schema ty' ϕ.
  Proof.
    rewrite /query_conforms.
    move/andP=> [/nilP HNnil Hlook].
    move: Hlook.
    case H : lookup_field_in_type => [fld'|] //.
    move/andP=> [Hargs Hall].
    rewrite -/(query_conforms schema fld') in Hall.
    rewrite /queries_conform.
    exists (fld'.(return_type)).
    by apply/andP; split => //; case eqP. 
  Qed.

  Lemma nf_queries_conform'' schema ty n α ϕ fld :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedField n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    move=> Hlook; rewrite /query_conforms.
    move/andP=> [/nilP HNnil].
    rewrite Hlook.
    move/andP=> [_]. rewrite -/(query_conforms schema fld).
    move=> Hall.
    rewrite /queries_conform.
      by apply/andP; split => //; case eqP.
  Qed.
    
    
  Lemma lookup_field_or_type schema lookup_type ty name fld :
    lookup_field_in_type schema lookup_type name = Some fld ->
    lookup_field_type schema lookup_type name = Some ty ->
    ty = fld.(return_type).
  Proof.
    by rewrite /lookup_field_type; move=> ->; case. Qed.

  Lemma nf_queries_correct schema root current n α ϕ fld :
    lookup_field_type schema current n = Some fld ->
    Correct schema (root, current) (NestedField n α ϕ) ->
    Forall (Correct schema (name_of_type fld, name_of_type fld)) ϕ.
  Proof.  by move=> Hlook H; inversion H; rewrite Hlook in H6; case: H6 => ->. Qed.


  Lemma nf_queries_eq schema (g : @conformedGraph N Name Vals schema) u n α ϕ ϕ' :
    (forall v, eval_queries schema g v ϕ = eval_queries schema g v ϕ') ->
    eval schema g u (NestedField n α ϕ) = eval schema g u (NestedField n α ϕ').
  Proof.
    rewrite /eval_queries.
    move=> Hqs.
    rewrite /eval.
    case lookup_field_type => //.
    case=> [nt | lt].
    case get_target_nodes_with_field => // v1 vn /=.
    by rewrite -/(eval schema g v1); move: (Hqs v1) => ->. 
    case get_target_nodes_with_field => // v1 vn /=.
    rewrite -/(eval schema g v1). move: (Hqs v1) => ->.
  Admitted.
    

  Theorem all_q_has_nrgtnf_q schema (g : @conformedGraph N Name Vals schema) u root (ϕ : @Query Name Vals):
    u \in nodes g ->
    query_conforms schema u.(type) ϕ ->
    Correct schema (root, u.(type)) ϕ ->
    exists (ϕ' : @Query Name Vals),
      [/\ is_in_normal_form ϕ' ,
       is_non_redundant ϕ' ,
       AtomicQueryRed schema ϕ ϕ' &
       QueryEq g u u.(type) ϕ ϕ'].
  Proof.
    elim ϕ using Query_ind with
        (Pl := fun qs => forall v root,
                  v \in nodes g ->
                  queries_conform schema v.(type) qs ->
                  Forall (Correct schema (root, v.(type))) qs ->    
                  exists (qs' : seq Query),
                    [/\ are_in_normal_form qs',
                     are_non_redundant qs',
                     QueryRed schema qs qs' &
                     QueriesEq g v v.(type) qs qs']).
    - by move=> n α; exists (SingleField n α); split => //; constructor.
    - by move=> l n α; exists (LabeledField l n α); split => //; constructor.
    - move=> n α qs IH Huin Hqc Hok.
      move: (nf_conforms_lookup_some Hqc); case=> fld Hlook.
      move: (nf_queries_conform'' Hlook Hqc) => Hqsc.
      move: (nf_correct_lookup_some Hok); case=> ty' Hlook'.
      move: (nf_queries_correct Hlook' Hok).
      move: Hqsc.
      move: (lookup_field_or_type Hlook Hlook') => <- Hqsc Hqsok.
      pose target_nodes := get_target_nodes_with_field g u (Field n α).
      case: ty' Hlook' Hqsc Hqsok => [nt | lt].
      pose hd := ohead target_nodes.
      move: IH. case=> v.
      case=> qs' [Hnfs Hnrs Hreds Heqs].
      exists (NestedField n α qs'); split => //=.
      constructor. done.
      rewrite /QueryEq. move=> _ Hqsc'.
      rewrite /eval /=. rewrite Hlook'.
      case ty'.
      
      
    move=> ϕ.
    elim: ϕ ty ty' => [//| hd tl IH] ty ty'.
    case: tl IH.
    move/(_ ty ty').
    case=> //=. move: empty_queries_N_conform. move/(_ schema ty'). 
    move/queries_conform_cons.
    move=> ϕ; elim: ϕ ty ty'.
    - by move=> n α ty ty' Hc; exists (SingleField n α); split => //; constructor.
    - by move=> l n α ty ty' Hc; exists (LabeledField l n α); split => //; constructor.
    - move=> n α ϕ.
      move=> IH ty ty' Hc; move: (correct_conforms Hc) => Hcnfs.
      move: (nested_conforms_list Hcnfs) => Hnnil.
      move: (not_nil_spread Hnnil); case=> hd; case=> tl.
      case: hd => n' α' H.
      rewrite H in IH. move: (Forall_cons_inv IH) => [Hhd Htl].
      rewrite H in Hc. inversion Hc.
      move: (Forall_cons_inv H7) => [H'c H''].
      move: (Hhd ty'0 ty'0 H'c).
      rewrite H. move: (Hhd single_field_correct).
      exists (NestedField n α ((SingleField n' α') :: (filter (predC1 (SingleField n' α')) tl))).
      split => //=.
      case: hd H IH Hhd.
      
    - move=> q Hex /Correct_SQE /Hex; case=> q' [Hnf Hnr Hred Heq].
      exists (SingleQuery q'); split => //. 
      * by constructor.
      by rewrite /QueryEq => H1 H2; rewrite /eval -/(eval_query _) Heq.
    - case.  (* Check head of query list *)
      (* f[α] ϕ_1 ... ϕ_k *)
      * move=> n α Hex qs Hex' /Correct_SSE [H1 H2].
        (* Get the q' witness for f[α] and its properties *)
        move: {Hex} (Hex H1); case=> q' [Hnf Hnr /AQR_SFE -> Heq].
        (* Get the qs' witness for the tail (ϕ_1 ... ϕ_k) and its properties *)
        move: {Hex'} (Hex' H2); case=> qs' [Hnf' Hr' Hred' Heq'].
        move: (normal_form_fld_inline Hnf') => [/allP Hflds | /allP Hinlines].
        pose filtered := (filter (predC1 (SingleField n α)) qs').
        case E: filtered => [ϕ'|].
        exists (SelectionSet (SingleField n α) ϕ'); split => //.
        
        rewrite is_ground_typed_normal_form_equation_2.
        
        rewrite /filtered in E.
        apply/and3P; split => //.
        apply/orP; left => /=.
        apply: (query_filter_preserves Hflds E).
        apply: (filter_preserves_normal Hnf' E).
        simpl. apply: (filter_preserves_non_redundancy Hr' E).
        constructor.
        rewrite -E. apply/eqP.
        
      
    Admitted.

    
End Eq.