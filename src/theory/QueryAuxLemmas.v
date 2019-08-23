From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Query.
Require Import QueryAux.


Require Import SeqExtra.
Require Import Ssromega.

Require Import GeneralTactics.



(**
   This tactic breaks down a query and introduces its contents.
 *)
Ltac case_query q :=
  repeat match goal with
         | [H : context [q] |- _] => move: H
         | [|- _] =>
           let l := fresh "l" in
           let f := fresh "f" in
           let α := fresh "α" in
           let β := fresh "β" in
           let t := fresh "t" in
           case: q => [f α | l f α | f α β | l f α β | t β]
         end.

Section Theory.
  
  Ltac apply_andP := apply/andP; split => //.
  Transparent oqresponse_name qresponse_name is_field.

  Variables Vals : eqType.

  Implicit Type φ : seq (@Query Vals).
  Implicit Type query : @Query Vals.


  Section DefPreds.
    Variable (s : @wfGraphQLSchema Vals).

    (**
       This lemma states that an Object type [ty] always 
       applies to itself (See also [does_fragment_type_apply]).
     *)
    Lemma object_applies_to_itself ty :
      is_object_type s ty ->
      does_fragment_type_apply s ty ty.
    Proof.
        by rewrite /does_fragment_type_apply => ->.
    Qed.
    
  End DefPreds.
  
  Section Size.

    (**
       Equality lemma for queries_size without Equations. 
       It shows equality to the [sumn] function defined in SSreflect.
     *)
    Lemma queries_size_sumn φ :
      queries_size φ = sumn [seq query_size q | q <- φ].
    Proof.
        by elim: φ => //= q φ IH; case: q => /= *; simp query_size; rewrite IH.
    Qed.
    
    (**
       This lemma states that [queries_size] distributes over list concatenation.
     *)
    Lemma queries_size_cat φ φ' :
      queries_size (φ ++ φ') = queries_size φ + queries_size φ'.
    Proof.
      elim: φ φ' => //= hd tl IH φ'.
        by rewrite (IH φ') addnA.
    Qed.

    
    (**
       This lemma states that if [queries_size] is 0, that means the list is empty.
     *)
    Lemma queries_size_0_nil (qs : seq (@Query Vals)) : queries_size qs == 0 -> qs = [::].
    Proof.
        by case: qs => //=; case.
    Qed.

    (**
       This lemma states that if [queries_size_aux] is 0, that means the list is empty.
     *)
    Lemma queries_size_aux_0_nil (nq : seq (Name * @Query Vals)) : queries_size_aux nq == 0 -> nq = [::].
    Proof.
        by case: nq => //=; case=> ty; case.
    Qed.
      
  End Size.



  Section Find.
    Variable (s : @wfGraphQLSchema Vals).

    (**
       This lemma states that the size of the queries found via [find_queries_with_label] is
       less or equal to the original queries list.
     *)
    Lemma found_queries_leq_size l O__t qs :
      queries_size (find_queries_with_label s l O__t qs) <= queries_size qs.
    Proof.
        by funelim (find_queries_with_label _ _ _ qs) => //=; simp query_size; rewrite ?queries_size_cat; ssromega.
    Qed.

    (**
       This lemma states that that [find_queries_with_label] distributes over list concatenation.
     *)
    Lemma find_queries_with_label_cat l ty (qs1 qs2 : seq (@Query Vals)):
      find_queries_with_label s l ty (qs1 ++ qs2) = find_queries_with_label s l ty qs1 ++ find_queries_with_label s l ty qs2.
    Proof.
      funelim (find_queries_with_label s l ty qs1) => //=.
      all: do ? by simp find_queries_with_label; rewrite Heq /= H.
        by simp find_queries_with_label; rewrite Heq /= H0 catA.
    Qed.


    (**
       This lemma states that the size of the queries found via [find_fields_with_response_name] is
       less or equal to the original queries list.
     *)
    Lemma found_fields_leq_size k φ :
      queries_size (find_fields_with_response_name k φ) <= queries_size φ.
    Proof.
      funelim (find_fields_with_response_name k φ) => //=; simp query_size; do ? ssromega.
        by rewrite queries_size_cat; ssromega.
    Qed.

    (**
       This lemma states that
     *)
    Lemma find_map_inline_nil_func (f : Name -> seq (@Query Vals) -> seq Query) rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_queries_with_label s rname t [seq InlineFragment t' (f t' φ) | t' <- ptys] = [::].
    Proof.      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_queries_with_label.
      have -> /= : does_fragment_type_apply s t t' = false.
      rewrite /does_fragment_type_apply Hobj /=. 
        by move/memPn: Htnin => /(_ t' (mem_head t' ptys)) /negbTE; rewrite eq_sym.
        apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.

    
    Lemma find_map_inline_nil rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_queries_with_label s rname t [seq InlineFragment t' φ | t' <- ptys] = [::].
    Proof.
      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_queries_with_label.
      have -> /= : does_fragment_type_apply s t t' = false.
      rewrite /does_fragment_type_apply Hobj /=. 
        by move/memPn: Htnin => /(_ t' (mem_head t' ptys)) /negbTE; rewrite eq_sym.
        apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.

    (**
       This lemma states that if two response names are not equal, then you 
       can swap the order of filtering and finding queries with each respective response name,
       because they do not interfere between each other.
     *)
    Lemma find_filter_swap rname1 rname2 ty φ :
      rname1 == rname2 = false ->
      find_queries_with_label s rname1 ty (filter_queries_with_label rname2 φ) = (find_queries_with_label s rname1 ty φ).
    Proof.
      move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
      elim: n φ => /= [| n IH] φ; first by rewrite leqn0 => /queries_size_0_nil ->.
      case: φ => //= q φ; case_query q; simp query_size => Hleq Hneq; simp filter_queries_with_label; simp find_queries_with_label => /=; last first.

      - by case does_fragment_type_apply => /=; [congr cat|]; apply: IH => //; ssromega.

        all: do [case: eqP => /= [-> | Hfneq];
                             [ by rewrite eq_sym Hneq /=; apply: IH => //; ssromega
                             | by case: eqP => //= [/eqP Heq | /eqP-/negbTE Hfneq'];
                                              simp find_queries_with_label => /=; rewrite ?Heq ?Hfneq' /= IH //; ssromega ] ].
    Qed.
          

    (**
       This lemma states that if you try to find queries with a given response name after 
       you filtered those queries, then the result is empty.
     *)
    Lemma find_queries_filter_nil rname O__t φ :
      find_queries_with_label s rname O__t (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; do ? by simp find_queries_with_label; move/negbTE in Heq; rewrite Heq /=.
        by simp find_queries_with_label; case: does_fragment_type_apply => //=; rewrite H H0 /=.
    Qed.

    
    (**
       This lemma states that if you try to find every field with a given response name after 
       you filtered those queries, then the result is empty.
     *)
    Lemma find_fields_filter_nil rname φ :
      find_fields_with_response_name rname (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; do ? by simp find_fields_with_response_name; move/negbTE in Heq; rewrite Heq /=.
        by simp find_fields_with_response_name; rewrite H H0 /=.
    Qed.


    (**
       This lemma states that queries found via [find_queries_with_label] is a subsequence of 
       the fields found via [find_fields_with_response_name].
     *)
    Lemma find_queries_subseq_find_fields ty f φ :
      subseq (find_queries_with_label s f ty φ) (find_fields_with_response_name f φ).
    Proof.
      funelim (find_queries_with_label s f ty φ) => //=.
      all: do ?[simp find_fields_with_response_name; rewrite Heq /=; case: ifP => //=; by move/negbT/eqP].

      all: do ? by simp find_fields_with_response_name; rewrite Heq /=.

      - by simp find_fields_with_response_name; rewrite cat_subseq.
      - simp find_fields_with_response_name.
        rewrite -[find_queries_with_label _ _ _ _]cat0s; rewrite cat_subseq //=.
          by apply: sub0seq.
    Qed.

    (**
       This lemma states that if no field is found via [find_fields_with_response_name] then
       no field will be found via [find_queries_with_label] (because the latter is a subsequence of the former).
     *)
    Lemma find_queries_nil_if_find_fields_nil ty rname φ :
      find_fields_with_response_name rname φ = [::] ->
      find_queries_with_label s rname ty φ = [::].
    Proof.
      move=> Hnil.
      have := (find_queries_subseq_find_fields ty rname φ).
        by rewrite Hnil subseq0 => /eqP ->.
    Qed.
      
    
    (**
       This lemma states that projecting the second element of each element obtained
       with [find_pairs_with_response_name] is the same as first projecting the second element 
       and then applying [find_fields_with_response_name].
     *)
    Lemma find_pairs_spec rname (nq : seq (Name * @Query Vals)) :
      [seq q.2 | q <- find_pairs_with_response_name rname nq] = find_fields_with_response_name rname [seq q.2 | q <- nq].
    Proof.
      move: {2}(queries_size_aux _) (leqnn (queries_size_aux nq)) => n.
      rewrite /queries_size_aux.
      elim: n nq => /= [| n IH] nq; first by rewrite leqn0 => /queries_size_aux_0_nil ->.
      case: nq => //=; case=> /= ty q φ; case_query q;
                              rewrite /queries_size_aux /=; simp query_size => Hleq;
                              simp find_pairs_with_response_name;
                              simp find_fields_with_response_name => /=; do ? case: eqP => //= _; rewrite ?IH //; do ? ssromega.
      rewrite map_cat; congr cat; rewrite IH //=; do ? ssromega.
        by have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      by ssromega.
    Qed.


    (**
       This lemma states that inlining queries with type conditions and then searching for
       fragments with a type condition that was not in the original list of type conditions
       results in a empty list.

       See also:
       - [normalize_are_non_redundant]
       - [normalize_queries_are_non_redundant]
     *)
    Lemma find_fragment_inlined_nil_func t ptys (f : Name -> seq (@Query Vals) -> seq (@Query Vals)) φ :
      t \notin ptys ->
      find_fragment_with_type_condition t [seq InlineFragment t' (f t' φ) | t' <- ptys] = [::].
    Proof.
      elim: ptys => //= t' ptys IH.
      rewrite inE; bcase; simp find_fragment_with_type_condition.
        by move/negbTE in Hb1; rewrite Hb1 /=; apply: IH.
    Qed.

    (**
       This lemma states that if every inline fragment in a list 
       of inline fragments does not apply to a type [ty], then 
       [find_queries_with_label] will result in an empty list
       if [ty] is used to search.

       See also :
       - [exec_grounded_inlines_nil]
     *)
    Lemma find_fragment_not_applies_is_nil rname ty φ :
      all (fun q => q.(is_inline_fragment)) φ ->
      all (fun q => match q with
                 | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                 | _ => true
                 end) φ ->
      find_queries_with_label s rname ty φ = [::].
    Proof.
      funelim (find_queries_with_label s rname ty φ) => //=; bcase; [by rewrite Heq in Hb0 | by apply: H].
    Qed.
      

    
  End Find.

  Section Filter.
    Hint Resolve found_queries_leq_size.

      
    (**
       This lemma states that the size of filtered queries is less or 
       equal than the size of the original list of queries.
     *)
    Lemma filter_queries_with_label_leq_size l φ :
      queries_size (filter_queries_with_label l φ) <= queries_size φ.
    Proof.
      funelim (filter_queries_with_label l φ) => //=; do ?[simp query_size; ssromega]. 
    Qed.


    (**
       This lemma states that [filter_queries_with_label] distributes over list concatenation.
     *)
    Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Vals)) :
      filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
    Proof.
      elim: qs1  => //= hd tl IH.
      case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
        by rewrite IH.
    Qed.


    (**
       This lemma states that the order of filtering with two response names does not affect the result.
     *)
    Lemma filter_swap rname1 rname2 (φ : seq (@Query Vals)) :
      filter_queries_with_label rname1 (filter_queries_with_label rname2 φ) =
      filter_queries_with_label rname2 (filter_queries_with_label rname1 φ).
    Proof.
      funelim (filter_queries_with_label rname1 φ) => //=; do ? by simp filter_queries_with_label; case: eqP => //= _; simp filter_queries_with_label; rewrite Heq /= H.
      by simp filter_queries_with_label; rewrite H H0.
    Qed.

    (**
       This lemma states that filtering twice with the same response name is the same 
       as filtering once.
     *)
    Lemma filter_filter_absorb rname (φ : seq (@Query Vals)) :
      filter_queries_with_label rname (filter_queries_with_label rname φ) = filter_queries_with_label rname φ.
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; simp filter_queries_with_label; do ? by rewrite Heq /= H.
        by rewrite H H0.
    Qed.
     

    (**
       This lemma states that
     *)
    Lemma filter_map_inline_func (f : Name -> seq (@Query Vals) -> seq Query) rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t (f t φ) | t <- ptys] =
      [seq @InlineFragment Vals t (filter_queries_with_label rname (f t φ)) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.

    (**
       This lemma states that
     *)
    Lemma filter_map_inline rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t φ | t <- ptys] =
      [seq InlineFragment t (filter_queries_with_label rname φ) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.


   
    

    (**
       This lemma states that if there is no field with response name [rname],
       then filtering a list of fields by that response name will have no effect.

       This is not valid if there is an inline fragment, because filtering may 
       remove some of its subqueries.

       See also:
       - [exec_equivalence]
     *)
    Lemma filter_find_fields_nil_is_nil rname φ :
      all (fun q => q.(is_field)) φ ->
      find_fields_with_response_name rname φ = [::] ->
      filter_queries_with_label rname φ = φ.
    Proof.
      funelim (filter_queries_with_label rname φ) => //; simp find_fields_with_response_name.
      all: do ? [by move/negbTE in Heq; rewrite Heq /=; intros; rewrite H].
      all: do ? [by move/negbFE in Heq; rewrite Heq /=;intros; rewrite H].
    Qed.                                                                                                 
     
    (**
       This lemma states that filtering inline fragments via response name 
       preserves the fact that they are all inline fragments.

       See also:
       - [exec_grounded_inlines_nil]
     *)
    Lemma filter_preserves_inlines rname φ :
      all (fun q => q.(is_inline_fragment)) φ ->
      all (fun q => q.(is_inline_fragment)) (filter_queries_with_label rname φ).
    Proof.
        by funelim (filter_queries_with_label rname φ) => //=.
    Qed.

    Variable (s : @wfGraphQLSchema Vals).

    (**
       This lemma states that if any inline fragment in a list [φ] does 
       not apply to a type [ty], then filtering that list will preserve 
       the fact that inline fragments do not apply to [ty].

       See also:
       - [exec_grounded_inlines_nil]
     *)
    Lemma filter_preserves_fragment_not_applies ty rname φ :
      all (fun q : Query => match q with
                             | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                             | _ => true
                         end) φ ->
      all (fun q : Query => match q with
                             | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                             | _ => true
                             end) (filter_queries_with_label rname φ).
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; bcase; do ? by intros; apply: H.
        by apply_andP; apply: H0.
    Qed.

     (**
       This lemma states that if there is no field with response name [rname1], 
       then filtering will preserve the fact that there is no query with 
       response name [rname1].

       See also:
       - [filter_preserves_non_redundancy]
     *)
    Lemma filter_preserves_find_fields_nil rname1 rname2 φ :
      find_fields_with_response_name rname1 φ = [::] ->
      find_fields_with_response_name rname1 (filter_queries_with_label rname2 φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname2 φ) => //=; simp find_fields_with_response_name.
      move/cat_nil=> [Hnil1 Hnil2]; rewrite H // H0 //.
      all: do [by case: eqP => //= _; apply: H].
    Qed.
      
      
    (**
       This lemma states that if no inline fragment matches the type condition [t] then 
       [filter_queries_with_label] won't have any effect on this.

       See also:                  
       - [filter_preserves_non_redundancy]
     *)
    Lemma filter_preserves_find_frags_nil rname ty φ :
      find_fragment_with_type_condition ty φ = [::] ->
      find_fragment_with_type_condition ty (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; simp find_fragment_with_type_condition.
        by case: eqP => //= _; apply: H0.
    Qed.
      
    (**
       This lemma states that
     *)
    Lemma filter_pairs_spec rname (nq : seq (Name * @Query Vals)) :
      [seq q.2 | q <- filter_pairs_with_response_name rname nq] = filter_queries_with_label rname [seq q.2 | q <- nq].
    Proof.
      elim: nq => //= q nq IH.
        by case: q => ty; case=> //= [f α | l f α | f α β | l f α β | t β];
                                 simp filter_pairs_with_response_name;
                                 simp filter_queries_with_label => /=; do ? case: eqP => //= _; rewrite IH.
    Qed.
      
      
      
  End Filter.

  Section Merging.

    (**
       This lemma states that [merge_selection_sets] distributes over list concatenation.
     *)
    Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Query Vals)) :
      merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
    Proof.
        by rewrite /merge_selection_sets map_cat flatten_cat.
    Qed.
    
    (**
       This lemma states that the size of queries obtained via [merge_selection_sets]
       is less or equal than the size of the original list of queries.
     *)
    Lemma merged_selections_leq φ :
      queries_size (merge_selection_sets φ) <= queries_size φ.
    Proof.
      rewrite /merge_selection_sets.
        by elim: φ => //=; case=> //= *; simp query_size; rewrite ?queries_size_cat; ssromega.
    Qed.


    Variable (s : @wfGraphQLSchema Vals).

     (**
       This lemma states that the size of queries obtained via [merge_pairs_selection_sets]
       is less or equal than the size of the original list of queries.
     *)
    Lemma merge_pair_selections_leq (nq : seq (Name * @Query Vals)) :
      queries_size_aux (merge_pairs_selection_sets s nq) <= queries_size_aux nq.
    Proof.
      rewrite /queries_size_aux; funelim (merge_pairs_selection_sets s nq) => //=; simp query_size; do ? ssromega;
      have Hpeq : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      all: do ? [by rewrite map_cat queries_size_cat Hpeq; ssromega].
    Qed.

    
  End Merging.

End Theory.









(* Unused lemmas *)

 (* Lemma query_size_gtn_0 query : *)
    (*   0 < query_size query. *)
    (* Proof. *)
    (*     by case: query. *)
    (* Qed. *)

    (* Lemma subqueries_lt_query query : *)
    (*   queries_size query.(qsubqueries) < query_size query. *)
    (* Proof. *)
    (*     by case: query. *)
    (* Qed. *)


    
    (* Lemma in_queries_lt query φ : *)
    (*   query \in φ -> *)
    (*         query_size query <= queries_size φ. *)
    (* Proof. *)
    (*   elim: φ => //= q φ IH. *)
    (*   rewrite inE => /orP [/eqP -> | Hin]. *)
    (*     by ssromega. *)
    (*       by move: (IH Hin) => Hlt; ssromega. *)
    (* Qed. *)

    (* Lemma in_subqueries_size_lt query1 query : *)
    (*   query1 \in query.(qsubqueries) -> *)
    (*          query_size query1 < query_size query. *)
    (* Proof. *)
    (*   move=> Hin. *)
    (*   have Hlt := (subqueries_lt_query query). *)
    (*   have Hleq := (in_queries_lt Hin). *)
    (*   ssromega. *)
    (* Qed. *)


 (* Section DefPreds. *)
    
  (*   Variable (s : @wfSchema Vals). *)
    
  (*   Lemma is_definedE q (Hfield : q.(is_field)) ty : *)
  (*     is_defined s q Hfield ty -> *)
  (*     exists fld, lookup_field_in_type s ty (qname q Hfield) = Some fld. *)
  (*   Proof. *)
  (*     funelim (is_defined _ _ _ _) => //=. *)
  (*       by rewrite /isSome; case lookup_field_in_type => //= fld _; exists fld. *)
  (*   Qed. *)

  (*   Lemma are_defined_cat φ1 φ2 ty : *)
  (*     are_defined s (φ1 ++ φ2) ty = are_defined s φ1 ty && are_defined φ2 ty. *)
  (*   Proof. *)
  (*     funelim (are_defined φ1 ty) => //=; simp are_defined is_defined => /=; rewrite ?H ?H0 ?andbA //. *)
  (*   Qed. *)
(* End DefPreds. *)



    (* Lemma found_queries_are_fields k O__t qs : *)
    (*   all (fun q => q.(is_field)) (find_queries_with_label s k O__t qs). *)
    (* Proof. *)
    (*   by funelim (find_queries_with_label s k O__t qs) => //=; rewrite all_cat; apply_andP. *)
    (* Qed. *)

   (* Lemma found_queries_have_response_name rname O__t qs : *)
    (*   forall q, q \in find_queries_with_label s rname O__t qs -> *)
    (*              q.(oqresponse_name) = Some rname. *)
    (* Proof. *)
    (*   funelim (find_queries_with_label s rname O__t qs) => //= q; rewrite ?inE. *)

    (*   all: do ? [move=> /orP [/eqP -> /= | Hin] ]. *)
    (*   all: do ? [by simpl in Heq; move/eqP in Heq; congr Some]. *)
    (*   all: do ?[by apply: H].     *)
    (*     by rewrite mem_cat => /orP [Hin1 | Hin2]; [apply: H | apply: H0]. *)
    (* Qed. *)
    

    
    (* Lemma all_found_fields_are_fields k φ : *)
    (*   all (fun query => query.(is_field)) (find_fields_with_response_name k φ).                   *)
    (* Proof. *)
    (*   funelim (find_fields_with_response_name k φ) => //=. *)
    (*     by rewrite all_cat; apply_andP. *)
(* Qed. *)

 (* Lemma find_map_inline_nil_get_types rname t ty φ : *)
    (*   t \notin get_possible_types s ty -> *)
    (*   find_queries_with_label s rname t [seq InlineFragment t' φ | t' <- get_possible_types s ty] = [::]. *)
    (* Proof. *)
    (*     by move=> Hnin; apply: find_map_inline_nil => //=; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object]. *)
    (* Qed. *)

    
    (* Lemma find_all_q_equiv_to_sf_are_simple α f ty φ : *)
    (*   all (are_equivalent (SingleField f α)) (find_queries_with_label s f ty φ) -> *)
    (*   all (fun query => query.(is_simple_field_selection)) (find_queries_with_label s f ty φ). *)
    (* Proof. *)
    (*   funelim (find_queries_with_label s f ty φ) => //=. *)

    (*   all: do ? by case/andP=> *; apply_andP; apply: (H α). *)
    (*   all: do ? by move=> *; apply: (H α). *)

    (*     by rewrite 2!all_cat => /andP [Hall1 Hall2]; apply_andP; [apply: (H α) | apply: (H0 α)]. *)

    (* Qed. *)

    
    (* Lemma find_all_f_equiv_to_sf_are_simple ty f α (φ : seq (@Query Vals)) : *)
    (*   all (are_equivalent (SingleField f α)) (find_fields_with_response_name f φ) -> *)
    (*   all (fun q => q.(is_simple_field_selection)) (find_queries_with_label s f ty φ). *)
    (* Proof. *)
    (*   funelim (find_queries_with_label s f ty φ) => //=. *)

    (*   all: do ?[by simp find_fields_with_response_name; rewrite Heq /= => /andP [Hequiv Hequivs]; apply_andP; apply: (H α)]. *)

    (*   all: do ? by simp find_fields_with_response_name; rewrite Heq /= => *; apply: (H α). *)

    (*   - by simp find_fields_with_response_name; rewrite 2!all_cat => /andP [Hequiv Hequivs]; apply_andP; [apply: (H α) | apply: (H0 α)]. *)
    (*   - by simp find_fields_with_response_name; rewrite all_cat => /andP [Hequiv Hequivs]; apply: (H α). *)
        
    (* Qed. *)



   

    
    (* Lemma find_fields_cat rname φ1 φ2 : *)
    (*   find_fields_with_response_name rname (φ1 ++ φ2) = *)
    (*   find_fields_with_response_name rname φ1 ++ find_fields_with_response_name rname φ2. *)
(* Admitted. *)

  (* Lemma filter_fields_spec l φ : *)
    (*   all (fun q => q.(is_field)) φ -> *)
    (*   filter_queries_with_label l φ = [seq q <- φ | match q with *)
    (*                                                | SingleField f _ *)
    (*                                                | NestedField f _ _ => f != l *)
    (*                                                | LabeledField l' _ _ *)
    (*                                                | NestedLabeledField l' _ _ _ => l' != l *)
    (*                                                | _ => false *)
    (*                                                end ]. *)
    (* Proof. *)
    (*     by funelim (filter_queries_with_label l φ) => //= /andP [Hf Hflds]; rewrite Heq H. *)
    (* Qed. *)


 
    (* Lemma filter_find_nil f ty φ : *)
    (*   filter_queries_with_label f (find_queries_with_label s f ty φ) = [::]. *)
    (* Admitted. *)

    (* Lemma filter_find_swap f1 f2 ty φ : *)
    (*   filter_queries_with_label f1 (find_queries_with_label f2 ty φ) = find_queries_with_label f2 ty (filter_queries_with_label f1 φ). *)
(* Admitted.  *)


    
    (* Lemma merge_simple_fields_is_empty φ : *)
    (*   all (fun query => query.(is_simple_field_selection)) φ -> *)
    (*   merge_selection_sets φ = [::]. *)
    (* Proof. *)
    (*     by elim: φ => //=; case. *)
    (* Qed. *)



    (* Lemma filter_all rname (φ : seq (@Query Vals)) : *)
    (*   all (has_response_name rname) φ -> *)
    (*   filter_queries_with_label rname φ = [::]. *)
    (* Proof. *)
    (*     by elim: φ => //=; case=> //= [f' α | l f' α | f' α β | l f' α β] φ IH; simp has_response_name => /= /andP [/eqP Heq Hsame]; *)
    (*                                                                                                      simp filter_queries_with_label => /=;  *)
    (*                                                                                                                                         rewrite Heq /=; case: eqP => //= _; apply: IH. *)
    (* Qed. *)
    
    
    (* Lemma filter_frag (ptys : seq Name) f φ : *)
    (*   all (has_response_name f) φ -> *)
    (*   filter_queries_with_label f [seq InlineFragment t φ | t <- ptys] = *)
    (*   [seq InlineFragment t [::] | t <- ptys]. *)
    (* Proof. *)
    (*   move=> /filter_all Heq. *)
    (*   elim: ptys => //= q qs IHqs; simp filter_queries_with_label => /=. *)
    (*     by rewrite Heq IHqs. *)
    (* Qed. *)