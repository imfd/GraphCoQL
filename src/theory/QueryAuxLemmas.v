(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaLemmas.
Require Import SchemaWellFormedness.

Require Import Query.
Require Import QueryAux.


Require Import SeqExtra.
Require Import Ssromega.

Require Import GeneralTactics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Aux Theory</h1>
        <p class="lead">
         This file contains lemmas about the auxiliary definitions used with GraphQL Queries.
        </p>         
        <p>
        These are mostly auxiliary and bureaucratic lemmas, such as filter distributing over 
        concatenation, queries size equals to 0 means empty list, etc. 
        </p>
        <p>
        The most widely used are probably those related to showing that the queries size
        is reduced after applying a certain function (filtering, finding, merging, etc.).
        </p>
  </div>
</div>#
 *)


(**
   This tactic breaks down a query and introduces its contents.
 *)
Ltac case_selection q :=
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
  
  Transparent qresponse_name is_field.

  Variable (Scalar : eqType).

  Implicit Type φ : seq (@Selection Scalar).
  Implicit Type selection : @Selection Scalar.

  (** *** Other types of predicates *)
  (** ---- *)
  Section DefPreds.
    Variable (s : wfGraphQLSchema).

    
    (**
       This lemma states that an object type [ty] always 
       applies to itself.
     *)
    Lemma object_applies_to_itself ty :
      is_object_type s ty ->
      does_fragment_type_apply s ty ty.
    Proof.
      funelim (is_object_type s ty) => //=.
      rewrite /does_fragment_type_apply Heq.
        by move/lookup_type_name_wf: Heq => ->.
    Qed.


    (** ---- *)
    (**
       This lemma states that an object type different to another
       cannot apply to it.
     *)
    Lemma object_diff_name_N_applies ty ty' :
      is_object_type s ty' ->
      ty' != ty ->
      does_fragment_type_apply s ty ty' = false.
    Proof.
      rewrite /does_fragment_type_apply.
      funelim (is_object_type s ty') => //= _ /negbTE Hneq.
      case lookup_type => //=; case=> //=; rewrite Heq => _ _ _.
      move/lookup_type_name_wf: Heq => /= <-.
        by rewrite eq_sym.
    Qed.
    
  End DefPreds.

  (** *** Selection size 
  (** ---- *)
      
      In this section we define lemmas about selection size.
   *)
  Section Size.

    (** ---- *)
    (**
       Equality lemma for [selections_size] without Equations. 
       It shows equality to the [sumn] function defined in SSreflect.
     *)
    Lemma selections_size_sumn φ :
      selections_size φ = sumn [seq selection_size q | q <- φ].
    Proof.
        by elim: φ => //= q φ IH; case: q => /= *; simp selection_size; rewrite IH.
    Qed.


    (** ---- *)
    (**
       This lemma states that [selections_size] distributes over list concatenation.
     *)
    Lemma selections_size_cat φ φ' :
      selections_size (φ ++ φ') = selections_size φ + selections_size φ'.
    Proof.
      elim: φ φ' => //= hd tl IH φ'.
        by rewrite (IH φ') addnA.
    Qed.


    (** ---- *)
    (**
       This lemma states that if the size of queries is 0, that means the list is empty.
     *)
    Lemma selections_size_0_nil (qs : seq (@Selection Scalar)) : selections_size qs == 0 -> qs = [::].
    Proof.
        by case: qs => //=; case.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that if the size of queries is 0, that means the list is empty.
     *)
    Lemma selections_size_aux_0_nil (nq : seq (Name * @Selection Scalar)) : selections_size_aux nq == 0 -> nq = [::].
    Proof.
        by case: nq => //=; case=> ty; case.
    Qed.

    (** ---- *)
    (**
       This lemma states that [selections_size_aux] distributes over list concatenation.
     *)
    Lemma selections_size_aux_cat (σs1 σs2 : seq (Name * @Selection Scalar)) : 
      selections_size_aux (σs1 ++ σs2) = selections_size_aux σs1 + selections_size_aux σs2.
    Proof.
      case: σs1 σs2 => //= σ σs1 σs2.
      by rewrite /selections_size_aux /= map_cat selections_size_cat -?/(selections_size_aux _) addnA.
      
    Qed.

    (** ---- **)
    (**
       This lemma states that if the size of a selection set is less or equal to [n], then
       the size of the same selection, paired with a type, is also less or equal to [n].
     *)
    Lemma selections_size_aux_tr (σs : seq (@Selection Scalar)) t n :
      selections_size σs <= n ->
      selections_size_aux [seq (t, σ) | σ <- σs] <= n.
    Proof.
        by rewrite /selections_size_aux -map_comp /funcomp /= map_id.
    Qed.
      
  End Size.



  (** *** Find 
      ----

     Lemmas about functions used to find queries 
   *)
  Section Find.
    Variable (s : wfGraphQLSchema).

    (**
       This lemma states that the size of the selections found via [find_valid_fields_with_response_name] is
       less or equal to the original selection list.
     *)
    Lemma found_queries_leq_size l O__t (qs : seq (@Selection Scalar)) :
      selections_size (find_valid_fields_with_response_name s l O__t qs) <= selections_size qs.
    Proof.
        by funelim (find_valid_fields_with_response_name _ _ _ qs) => //=; simp selection_size; rewrite ?selections_size_cat; ssromega.
    Qed.

    
    (**
       This lemma states that the size of the selections found via [find_valid_pairs_with_response_name] is
       less or equal to the original selection list.
     *)
    Lemma found_valid_pairs_leq_size ts rname (σs : seq (Name * @Selection Scalar)) :
      selections_size_aux (find_valid_pairs_with_response_name s ts rname σs) <=
      selections_size_aux σs.
    Proof.
      funelim (find_valid_pairs_with_response_name s ts rname σs) => //=;
      rewrite /selections_size_aux /=; simp selection_size => /=; rewrite -?selections_size_cat -?/(selections_size_aux _);
      do ? ssromega.
      rewrite /selections_size_aux /= -map_comp /funcomp /= map_id -/(selections_size_aux _) in H.
      rewrite selections_size_aux_cat -?/(selections_size_aux _).
        by ssromega.
    Qed.
      
    (** ---- *)
    (**
       This lemma states that that [find_valid_fields_with_response_name] distributes over list concatenation.
     *)
    Lemma find_valid_fields_with_response_name_cat l ty (qs1 qs2 : seq (@Selection Scalar)):
      find_valid_fields_with_response_name s l ty (qs1 ++ qs2) = find_valid_fields_with_response_name s l ty qs1 ++ find_valid_fields_with_response_name s l ty qs2.
    Proof.
      funelim (find_valid_fields_with_response_name s l ty qs1) => //=.
      all: do ? by simp find_valid_fields_with_response_name; rewrite Heq /= H.
        by simp find_valid_fields_with_response_name; rewrite Heq /= H0 catA.
    Qed.

    (** ---- *)
    (**
       This lemma states that the size of the queries found via [find_fields_with_response_name] is
       less or equal to the original queries list.
     *)
    Lemma found_fields_leq_size k φ :
      selections_size (find_fields_with_response_name k φ) <= selections_size φ.
    Proof.
      funelim (find_fields_with_response_name k φ) => //=; simp selection_size; do ? ssromega.
        by rewrite selections_size_cat; ssromega.
    Qed.

    (** ---- *)
    (**
       This lemma states that the size of the queries found via [find_pairs_with_response_name] is
       less or equal to the original queries list.
     *)
    Lemma found_pairs_with_response_name_leq rname (σ : seq (Name * @Selection Scalar)) :
      selections_size_aux (find_pairs_with_response_name rname σ) <= selections_size_aux σ.
    Proof.
      rewrite /selections_size_aux.
      funelim (find_pairs_with_response_name rname σ) => //=; simp selection_size; do ? ssromega.
      rewrite map_cat selections_size_cat.
      rewrite -map_comp /funcomp map_id in H; ssromega.
    Qed.

    (** ---- *)
    (**
       This lemma states that finding selections in fragments, whose contents are modified by a function [f], with
       type conditions that do not apply to a given object type [t], result in an empty list.
     *)
    Lemma find_map_inline_nil_func (f : Name -> seq (@Selection Scalar) -> seq (@Selection Scalar)) rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_valid_fields_with_response_name s rname t [seq InlineFragment t' (f t' φ) | t' <- ptys] = [::].
    Proof.      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_valid_fields_with_response_name.
      have -> /= : does_fragment_type_apply s t t' = false.
        by apply: object_diff_name_N_applies => //; move/memPn: Htnin => /(_ t' (mem_head t' ptys)).
      apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.


    (** ---- *)
    (**
       This lemma states that finding selections in fragments with type conditions that
       do not apply to a given object type [t], result in an empty list.
     *)
    (* Unused *)
    Lemma find_map_inline_nil rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_valid_fields_with_response_name s rname t [seq InlineFragment t' φ | t' <- ptys] = [::].
    Proof.
      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_valid_fields_with_response_name.
      have -> /= : does_fragment_type_apply s t t' = false.
          by apply: object_diff_name_N_applies => //; move/memPn: Htnin => /(_ t' (mem_head t' ptys)).
      apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that if two response names are not equal, then you 
       can swap the order of filtering and finding queries with each respective response name,
       because they do not interfere between each other.
     *)
    Lemma find_filter_swap rname1 rname2 ty φ :
      rname1 == rname2 = false ->
      find_valid_fields_with_response_name s rname1 ty (filter_queries_with_label rname2 φ) = (find_valid_fields_with_response_name s rname1 ty φ).
    Proof.
      move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
      elim: n φ => /= [| n IH] φ; first by rewrite leqn0 => /selections_size_0_nil ->.
      case: φ => //= q φ; case_selection q; simp selection_size => Hleq Hneq; simp filter_queries_with_label; simp find_valid_fields_with_response_name => /=; last first.

      - by case does_fragment_type_apply => /=; [congr cat|]; apply: IH => //; ssromega.

        all: do [case: eqP => /= [-> | Hfneq];
                             [ by rewrite eq_sym Hneq /=; apply: IH => //; ssromega
                             | by case: eqP => //= [/eqP Heq | /eqP-/negbTE Hfneq'];
                                              simp find_valid_fields_with_response_name => /=; rewrite ?Heq ?Hfneq' /= IH //; ssromega ] ].
    Qed.
          

    (** ---- *)
    (**
       This lemma states that if you try to find queries with a given response name after 
       you filtered those queries, then the result is empty.
     *)
    Lemma find_queries_filter_nil rname O__t φ :
      find_valid_fields_with_response_name s rname O__t (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; do ? by simp find_valid_fields_with_response_name; move/negbTE in Heq; rewrite Heq /=.
        by simp find_valid_fields_with_response_name; case: does_fragment_type_apply => //=; rewrite H H0 /=.
    Qed.


    (** ---- *)
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


    (** ---- *)
    (**
       This lemma states that queries found via [find_valid_fields_with_response_name] is a subsequence of 
       the fields found via [find_fields_with_response_name].
     *)
    Lemma find_queries_subseq_find_fields ty f φ :
      subseq (find_valid_fields_with_response_name s f ty φ) (find_fields_with_response_name f φ).
    Proof.
      funelim (find_valid_fields_with_response_name s f ty φ) => //=.
      all: do ?[simp find_fields_with_response_name; rewrite Heq /=; case: ifP => //=; by move/negbT/eqP].

      all: do ? by simp find_fields_with_response_name; rewrite Heq /=.

      - by simp find_fields_with_response_name; rewrite cat_subseq.
      - simp find_fields_with_response_name.
        rewrite -[find_valid_fields_with_response_name _ _ _ _]cat0s; rewrite cat_subseq //=.
          by apply: sub0seq.
    Qed.


    (** ---- *)
    (**
       This lemma states that if no field is found via [find_fields_with_response_name] then
       no field will be found via [find_valid_fields_with_response_name] (because the latter is a subsequence of the former).
     *)
    Lemma find_queries_nil_if_find_fields_nil ty rname φ :
      find_fields_with_response_name rname φ = [::] ->
      find_valid_fields_with_response_name s rname ty φ = [::].
    Proof.
      move=> Hnil.
      have := (find_queries_subseq_find_fields ty rname φ).
        by rewrite Hnil subseq0 => /eqP ->.
    Qed.
      
    (** ---- *)
    (**
       This lemma states that projecting the second element of each pair obtained
       with [find_pairs_with_response_name] is the same as first projecting the second element 
       and then applying [find_fields_with_response_name].
     *)
    Lemma find_pairs_spec rname (nq : seq (Name * @Selection Scalar)) :
      [seq q.2 | q <- find_pairs_with_response_name rname nq] = find_fields_with_response_name rname [seq q.2 | q <- nq].
    Proof.
      move: {2}(selections_size_aux _) (leqnn (selections_size_aux nq)) => n.
      rewrite /selections_size_aux.
      elim: n nq => /= [| n IH] nq; first by rewrite leqn0 => /selections_size_aux_0_nil ->.
      case: nq => //=; case=> /= ty q φ; case_selection q;
                              rewrite /selections_size_aux /=; simp selection_size => Hleq;
                              simp find_pairs_with_response_name;
                              simp find_fields_with_response_name => /=; do ? case: eqP => //= _; rewrite ?IH //; do ? ssromega.
      rewrite map_cat; congr cat; rewrite IH //=; do ? ssromega.
        by have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      by ssromega.
    Qed.

    (** ---- *)
    (**
       This lemma states that inlining queries with type conditions and then searching for
       fragments with a type condition that was not in the original list of type conditions
       results in a empty list.
     *)
    Lemma find_fragment_inlined_nil_func t ptys (f : Name -> seq (@Selection Scalar) -> seq (@Selection Scalar)) φ :
      t \notin ptys ->
      find_fragment_with_type_condition t [seq InlineFragment t' (f t' φ) | t' <- ptys] = [::].
    Proof.
      elim: ptys => //= t' ptys IH.
      rewrite inE; bcase; simp find_fragment_with_type_condition.
        by move/negbTE in Hb1; rewrite Hb1 /=; apply: IH.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that if every inline fragment in a list 
       of inline fragments does not apply to a type [ty], then 
       [find_valid_fields_with_response_name] will result in an empty list
       if [ty] is used to search.
     *)
    Lemma find_fragment_not_applies_is_nil rname ty φ :
      all (fun q => q.(is_inline_fragment)) φ ->
      all (fun q => match q with
                 | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                 | _ => true
                 end) φ ->
      find_valid_fields_with_response_name s rname ty φ = [::].
    Proof.
      funelim (find_valid_fields_with_response_name s rname ty φ) => //=; bcase; [by rewrite Heq in Hb0 | by apply: H].
    Qed.
      

    
  End Find.


  (** *** Filter 
      ----

      Lemmas about filtering queries.
   *)
  Section Filter.
    Hint Resolve found_queries_leq_size.

    (**
       This lemma states that filtering pairs and projecting the second element is the same as 
       first projecting and then filtering.
     *)
    Lemma filter_pairs_spec rname (nq : seq (Name * @Selection Scalar)) :
      [seq q.2 | q <- filter_pairs_with_response_name rname nq] = filter_queries_with_label rname [seq q.2 | q <- nq].
    Proof.
      elim: nq => //= q nq IH.
        by case: q => ty; case=> //= [f α | l f α | f α β | l f α β | t β];
                                 simp filter_pairs_with_response_name;
                                 simp filter_queries_with_label => /=; do ? case: eqP => //= _; rewrite IH.
    Qed.
      
    
    (** ---- *)  
    (**
       This lemma states that the size of filtered selections is less or 
       equal than the size of the original list of selections.
     *)
    Lemma filter_queries_with_label_leq_size l φ :
      selections_size (filter_queries_with_label l φ) <= selections_size φ.
    Proof.
      funelim (filter_queries_with_label l φ) => //=; do ?[simp selection_size; ssromega]. 
    Qed.


    (** ---- **)
    (**
       This lemma states that the size of filtered selections is less or 
       equal than the size of the original list of selections.
     *)
    Lemma filter_pairs_with_response_name_leq rname (σ : seq (Name * @Selection Scalar)) :
      selections_size_aux (filter_pairs_with_response_name rname σ) <= selections_size_aux σ.
    Proof.
      rewrite /selections_size_aux.
      funelim (filter_pairs_with_response_name rname σ) => //=; simp selection_size; do ? [ssromega].
      have Hfleq := (filter_queries_with_label_leq_size response_name subselections2); ssromega.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that [filter_queries_with_label] distributes over list concatenation.
     *)
    Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Selection Scalar)) :
      filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
    Proof.
      elim: qs1  => //= hd tl IH.
      case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
        by rewrite IH.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that the order of filtering with two response names does not affect the result.
     *)
    Lemma filter_swap rname1 rname2 (φ : seq (@Selection Scalar)) :
      filter_queries_with_label rname1 (filter_queries_with_label rname2 φ) =
      filter_queries_with_label rname2 (filter_queries_with_label rname1 φ).
    Proof.
      funelim (filter_queries_with_label rname1 φ) => //=; do ? by simp filter_queries_with_label; case: eqP => //= _; simp filter_queries_with_label; rewrite Heq /= H.
      by simp filter_queries_with_label; rewrite H H0.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that filtering twice with the same response name is the same 
       as filtering once.
     *)
    Lemma filter_filter_absorb rname (φ : seq (@Selection Scalar)) :
      filter_queries_with_label rname (filter_queries_with_label rname φ) = filter_queries_with_label rname φ.
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; simp filter_queries_with_label; do ? by rewrite Heq /= H.
        by rewrite H H0.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that filtering a list of inline fragments is the same as filtering
       each fragments's subselections, even when they are modified by a function [f].
     *)
    Lemma filter_map_inline_func (f : Name -> seq (@Selection Scalar) -> seq Selection) rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t (f t φ) | t <- ptys] =
      [seq @InlineFragment Scalar t (filter_queries_with_label rname (f t φ)) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that
     *)
    (* Unused *)
    Lemma filter_map_inline rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t φ | t <- ptys] =
      [seq InlineFragment t (filter_queries_with_label rname φ) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.


     
    (** ---- *)
    (**
       This states that filtering a list of field selections by a response name [rname] 
       results in the same list, if no field has that response name.

       This is not valid if there is an inline fragment, because filtering may 
       remove some of its subselections.
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

    
    (** ---- *) 
    (**
       This lemma states that filtering fields in inline fragments 
       preserves the fact that they are all inline fragments.
     *)
    Lemma filter_preserves_inlines rname φ :
      all (fun q => q.(is_inline_fragment)) φ ->
      all (fun q => q.(is_inline_fragment)) (filter_queries_with_label rname φ).
    Proof.
        by funelim (filter_queries_with_label rname φ) => //=.
    Qed.

    
    Variable (s : wfGraphQLSchema).

    
    (** ---- *)
    (**
       This lemma states that if every inline fragment in a list [φ] does 
       not apply to a type [ty], then filtering that list will preserve 
       the fact that inline fragments do not apply to [ty].
     *)
    Lemma filter_preserves_fragment_not_applies ty rname φ :
      all (fun q : Selection => match q with
                             | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                             | _ => true
                         end) φ ->
      all (fun q : Selection => match q with
                             | on (t) {(_)} => ~~ does_fragment_type_apply s ty t
                             | _ => true
                             end) (filter_queries_with_label rname φ).
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; bcase; do ? by intros; apply: H.
        by apply_andP; apply: H0.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that if there is no field with response name [rname1], 
       then filtering will preserve the fact that there is no selection with 
       response name [rname1].
     *)
    Lemma filter_preserves_find_fields_nil rname1 rname2 φ :
      find_fields_with_response_name rname1 φ = [::] ->
      find_fields_with_response_name rname1 (filter_queries_with_label rname2 φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname2 φ) => //=; simp find_fields_with_response_name.
      
      move/cat_nil=> [Hnil1 Hnil2]; rewrite H // H0 //.
      all: do [by case: eqP => //= _; apply: H].
    Qed.

    
    (** ---- *)  
    (**
       This lemma states that if there is no inline fragment that matches the type condition [t] then 
       [filter_queries_with_label] will preserve this fact.
     *)
    Lemma filter_preserves_find_frags_nil rname ty φ :
      find_fragment_with_type_condition ty φ = [::] ->
      find_fragment_with_type_condition ty (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; simp find_fragment_with_type_condition.
        by case: eqP => //= _; apply: H0.
    Qed.

    

      
      
  End Filter.


  (** *** Merging 
      ----

      Lemmas about merging subqueries of queries.
   *)
  Section Merging.

    
    (** ---- *)
    (**
       This lemma states that [merge_selection_sets] distributes over list concatenation.
     *)
    Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Selection Scalar)) :
      merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
    Proof.
        by rewrite /merge_selection_sets map_cat flatten_cat.
    Qed.

    
    (** ---- *)
    (**
       This lemma states that the size of queries obtained via [merge_selection_sets]
       is less or equal than the size of the original list of queries.
     *)
    Lemma merged_selections_leq φ :
      selections_size (merge_selection_sets φ) <= selections_size φ.
    Proof.
      rewrite /merge_selection_sets.
        by elim: φ => //=; case=> //= *; simp selection_size; rewrite ?selections_size_cat; ssromega.
    Qed.


    Variable (s : wfGraphQLSchema).


    (** ---- *)
     (**
       This lemma states that the size of queries obtained via [merge_pairs_selection_sets]
       is less or equal than the size of the original list of queries.
     *)
    Lemma merge_pair_selections_leq (nq : seq (Name * @Selection Scalar)) :
      selections_size_aux (merge_pairs_selection_sets s nq) <= selections_size_aux nq.
    Proof.
      rewrite /selections_size_aux; funelim (merge_pairs_selection_sets s nq) => //=; simp selection_size; do ? ssromega;
      have Hpeq : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
      all: do ? [by rewrite map_cat selections_size_cat Hpeq; ssromega].
    Qed.

    
  End Merging.

End Theory.

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryAux.html' class="btn btn-light" role='button'> Previous ← Query Aux </a>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-info" role='button'>Next → Query Conformance</a>
    </div>#
 *)
