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

Section Eq.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Inductive Correct schema : @QuerySet Name Vals -> (@NamedType Name * @NamedType Name) -> Prop :=
  | CSQ : forall ϕ root current,
      Correct' schema ϕ (root, current) ->
      Correct schema (SingleQuery ϕ) (root, current)
              
  | CSS : forall ϕ ϕ' root current,
      Correct' schema ϕ (root, current) ->
      Correct schema ϕ' (root, current) ->
      Correct schema (SelectionSet ϕ ϕ') (root, current)
              
  with Correct' schema : Query -> (NamedType * NamedType) -> Prop :=
       | CF : forall f α root current,
           Correct' schema (SingleField f α) (root, current)

       | CLF : forall l f α root current,
           Correct' schema (LabeledField l f α) (root, current)

       | CNF : forall f α ϕ root current ty',
           lookup_field_type schema root f = Some ty' ->
           Correct schema ϕ (name_of_type ty', name_of_type ty') ->
           Correct' schema (NestedField f α ϕ) (root, current)

       | CNLF : forall l f α ϕ root current ty',
           lookup_field_type schema root f = Some ty' ->
           Correct schema ϕ (name_of_type ty', name_of_type ty') ->
           Correct' schema (NestedLabeledField l f α ϕ) (root, current)

       | CIF : forall root current t ϕ,
           current \in get_possible_types schema t ->
           Correct schema ϕ (root, t) ->
           Correct' schema (InlineFragment t ϕ) (root, current).
                    
         
  Lemma Correct_SQE schema ϕ ty : Correct schema (SingleQuery ϕ) ty ->
                                  Correct' schema ϕ ty.
  Proof. by move=> H; inversion H. Qed.

  Lemma Correct_SSE schema ϕ ϕ' ty : Correct schema (SelectionSet ϕ ϕ') ty ->
                                     Correct' schema ϕ ty /\ Correct schema ϕ' ty.
  Proof. by move=> H; inversion H. Qed.

  Definition QueryEq schema (g : @conformedGraph N Name Vals schema) (q1 q2 : QuerySet)  :=
    query_set_conforms schema q1 schema.(query_type) ->
    query_set_conforms schema q2 schema.(query_type) ->
    eval schema g g.(root) q1 = eval schema g g.(root) q2.

  

  Lemma inline_eq schema (g : @conformedGraph N Name Vals schema) : forall t ϕ,
      eval_query schema g g.(root) (InlineFragment t ϕ) = eval_query schema g g.(root) (InlineFragment t (SingleQuery (InlineFragment t ϕ))).
  Proof.
    move=> t ϕ; rewrite /eval_query /=.
    case: lookup_type => //.
    case=> //.
    by move=> *; case: eqP.
    by move=> *; case: declares_implementation.
    by move=> *; case: (_ \in _).
  Qed.

  Lemma inline_nested_empty schema (g : @conformedGraph N Name Vals schema) :
    forall t1 t2 ϕ,
      is_object_type schema t1 ->
      is_object_type schema t2 ->
      t1 <> t2 ->
      eval_query schema g g.(root) (InlineFragment t1 (SingleQuery (InlineFragment t2 ϕ))) = inr (Results [::]).
  Proof.
    move=> t1 t2 ϕ.
    funelim (is_object_type schema t1) => //.
    funelim (is_object_type schema0 t2) => //.
    move=> _ _ Hdiff.
    rewrite /eval_query Heq0.
    case: eqP => // <-.
    rewrite Heq.
    by case: eqP => // Ht1t2; rewrite Ht1t2 in Hdiff.
  Qed.

  Lemma inline_query_preserves schema (g : @conformedGraph N Name Vals schema):
    forall ϕ u,
      u \in nodes g.(graph) ->
      eval_query schema g u ϕ = eval_query schema g u (InlineFragment u.(type) (SingleQuery ϕ)).
  Proof.
    move=> ϕ u Hin; case: g Hin.
    move=> g Hr He Hf Hn /= Hin.
    rewrite /nodes_have_object_type in Hn.
    move/seq.allP /(_ u Hin): Hn.
    case: u Hin => id ty flds Hin. rewrite /type. funelim (is_object_type schema ty) => //.
    move=> _.
    case: ϕ.
    move=> name α. rewrite /eval_query. rewrite Heq.
    simpl.  Admitted.

    


  Fixpoint query_set_of_list (s : seq Query) : option (@QuerySet Name Vals) :=
    match s with
    | [::] => None
    | hd :: [::] => Some (SingleQuery hd)
    | hd :: tl => if query_set_of_list tl is Some q then
                   Some (SelectionSet hd q)
                 else
                   None
    end.

  Equations append_queries (qs1 qs2 : @QuerySet Name Vals) : @QuerySet Name Vals :=
    {
      append_queries (SingleQuery q1) q2 := SelectionSet q1 q2;
      append_queries (SelectionSet q1 q1') q2 := SelectionSet q1 (append_queries q1' q2)

    }.

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

  
    
  
  Inductive QueryRed (schema : @wfSchema Name Vals) : QuerySet -> QuerySet -> Prop :=
  | SQ1 : forall ϕ ϕ',
      AtomicQueryRed schema ϕ ϕ' ->
      QueryRed schema (SingleQuery ϕ) (SingleQuery ϕ')

  | SS1 : forall ϕ ϕ' ϕs,
      AtomicQueryRed schema ϕ ϕ' ->
      QueryRed schema (SelectionSet ϕ ϕs) (SelectionSet ϕ' ϕs)
                   
  | SF_None : forall (ϕ : @QuerySet Name Vals) n α,
      filter (predC1 (SingleField n α)) ϕ == None ->
      QueryRed schema (SelectionSet (SingleField n α) ϕ) (SingleQuery (SingleField n α))

  | SF_Some : forall (ϕ ϕ' : @QuerySet Name Vals) n α,
      filter (predC1 (SingleField n α)) ϕ == Some ϕ' ->
      QueryRed schema (SelectionSet (SingleField n α) ϕ) (SelectionSet (SingleField n α) ϕ')


  | LF_None :  forall (ϕ : @QuerySet Name Vals) l n α,
      filter (predC1 (LabeledField l n α)) ϕ == None ->
      QueryRed schema
               (SelectionSet (LabeledField l n α) ϕ)
               (SingleQuery (LabeledField l n α))

  | LF_Some : forall (ϕ ϕ' : @QuerySet Name Vals) l n α,
      filter (predC1 (LabeledField l n α)) ϕ == Some ϕ' ->
      QueryRed schema
               (SelectionSet (LabeledField l n α) ϕ)
               (SelectionSet (LabeledField l n α) ϕ')

  | NF_None : forall (ϕ β χ : @QuerySet Name Vals) (n : Name) (α α' : {fmap Name -> Vals}),
      let subqueries := foldr (fun q acc => if q is NestedField n' α' χ then
                                          if (n' == n) && (α == α') then
                                            append_queries acc χ
                                          else
                                            acc
                                        else
                                          acc) β ϕ
      in
      (filter (fun q => ~~(partial_query_eq (NestedField n α β) q)) ϕ) == None ->
      QueryRed schema (SelectionSet (NestedField n α β) ϕ)
                      (SingleQuery (NestedField n α subqueries))
               
  | NF_Some : forall (ϕ ϕ' β χ : @QuerySet Name Vals) (n : Name) (α α' : {fmap Name -> Vals}),
      let subqueries := foldr (fun q acc => if q is NestedField n' α' χ then
                                          if (n' == n) && (α == α') then
                                            append_queries acc χ
                                          else
                                            acc
                                        else
                                          acc) β ϕ
      in
      (filter (fun q => ~~(partial_query_eq (NestedField n α β) q)) ϕ) == Some ϕ' ->
      QueryRed schema (SelectionSet (NestedField n α β) ϕ)
                      (SelectionSet (NestedField n α subqueries) ϕ')
               
                
  | Inline_spread : forall t ϕ ϕ',
      QueryRed schema (SingleQuery (InlineFragment t (SelectionSet ϕ ϕ')))
                      (SelectionSet (InlineFragment t (SingleQuery ϕ)) (SingleQuery (InlineFragment t ϕ')))
        

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
      AtomicQueryRed schema (InlineFragment t (SingleQuery (InlineFragment t ϕ))) (InlineFragment t ϕ) 

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

  
                                                             
  Lemma normal_form_fld_inline (query_set : @QuerySet Name Vals) : is_ground_typed_normal_form query_set ->
                                                                   (forall q : Query, in_query q query_set -> is_field q) \/ (forall q : Query, in_query q query_set -> is_inline_fragment q).
  Proof.
    case: query_set => [q | q qs].
    - case: q=> //=; do ?[by move=> *; left => q; move/eqP <-].
      by move=> *; right => q'; move/eqP <-.
    - rewrite is_ground_typed_normal_form_equation_2.
        by move/and3P=> [/orP [Hf | Hi] _ _]; [left | right]; apply/allP.
  Qed.


  Lemma filter_all_predC1 (T : eqType) (s : seq T) (x : T) :
    [seq x' <- s | predC1 x x'] = [::] ->
    forall x', x' \in s -> x' = x.
    elim: s x => [//| n s' IH] x /=.
    case: ifP => //.
    case: eqP => // -> _ /IH H.
    by move=> x'; rewrite in_cons => /orP [/eqP ->|]; [|apply: H]. 
  Qed.


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
  Qed.

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

  Lemma filter_preserves_non_redundancy (queries ϕ' : @QuerySet Name Vals) p :
    is_non_redundant queries ->
    filter p queries = Some ϕ' ->
    is_non_redundant ϕ'.
  Proof.
    Admitted.
      
  Theorem all_q_has_nrgtnf_q schema (g : @conformedGraph N Name Vals schema) :
    forall  (ϕ : @QuerySet Name Vals),
      Correct schema ϕ (schema.(query_type), schema.(query_type)) ->
      exists (ϕ' : @QuerySet Name Vals),
        [/\ is_ground_typed_normal_form ϕ' ,
         is_non_redundant ϕ' ,
         QueryRed schema ϕ ϕ' &
         QueryEq g ϕ ϕ'].
  Proof.
    move=> ϕ.
    elim ϕ using QuerySet_ind with (P0 := fun q =>
                                           Correct' schema q (schema.(query_type), schema.(query_type)) ->
                                           exists q', [/\ is_query_in_normal_form q' , is_query_non_redundant q' ,
                                                  AtomicQueryRed schema q q' &
                                                  (query_conforms schema q schema.(query_type) ->
                                                   query_conforms schema q' schema.(query_type) ->
                                                   eval_query schema g g.(root) q = eval_query schema g g.(root) q')]).
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