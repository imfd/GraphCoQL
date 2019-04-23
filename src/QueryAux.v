From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap.

Require Import Query.

Require Import Ssromega.

Require Import SeqExtra.

Section QueryAux.

  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
    
  Variables Name Vals : ordType.

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.
  Implicit Type responses : seq (@ResponseObject Name Vals).

  (** Get the query's size, according to Jorge and Olaf's version **)
  Equations query_size query : nat :=
    {
      query_size (NestedField _ _ q') := 1 + queries_size q';
      query_size (NestedLabeledField _ _ _ q') => 1 + (queries_size q');
      query_size (InlineFragment _ q') => 1 + (queries_size q');
      query_size _ := 1
    }
  where
  queries_size queries : nat :=
    {
      queries_size [::] := 0;
      queries_size (cons hd tl) := query_size hd + queries_size tl
    }.

  Lemma queries_size_app qs qs' :
    queries_size (qs ++ qs') = queries_size qs + queries_size qs'.
  Proof.
    elim: qs qs' => //= hd tl IH qs'.
    by rewrite (IH qs') addnA.
  Qed.

  Lemma query_size_gtn_0 q :
    0 < query_size q.
  Proof.
      by case: q.
  Qed.

  Lemma subqueries_lt_query q :
    queries_size q.(qsubquery) < query_size q.
  Proof.
      by case: q.
  Qed.

  Lemma in_queries_lt q qs :
    q \in qs ->
          query_size q <= queries_size qs.
  Proof.
    elim: qs => //= hd tl IH.
    rewrite inE => /orP [/eqP -> | Hin].
      by ssromega.
      by move: (IH Hin) => Hlt; ssromega.
  Qed.
  
  (** Partial equality between queries.
      It basically ignores subqueries and only checks labels, names and arguments **)
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => [&& (l == l'), (n == n') & (α == α')]
    | InlineFragment t _, InlineFragment t' _ => t == t'
    | _, _ => false
    end.


  (** Boolean predicates to check what type the query is:
      - Fields : Everything not an inline fragment
      - Inline : An inline fragment 
   **)
  Equations is_field query : bool :=
    is_field (InlineFragment _ _) := false;
    is_field _ := true.

  Equations is_inline_fragment query : bool :=
    is_inline_fragment (InlineFragment _ _) := true;
    is_inline_fragment _ := false.                                           


  (** Get the response's size, according to Jorge and Olaf's version **)
  Equations response_size response : nat :=
    {
      response_size (Null _) := 3;
      response_size (SingleResult _ _) := 3;
      response_size (ListResult _ vals) := 4 + size vals;
      response_size (NestedResult _ r') := 4 + responses_size r';
      response_size (NestedListResult _ rs) := 4 + 2 * size rs + responses_size' rs
    }
  where
  responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    {
      responses_size [::] := 0;
      responses_size (cons hd tl) := response_size hd + responses_size tl
    }
  where responses_size' (responses : seq (seq (@ResponseObject Name Vals))) : nat :=
    {
      responses_size' [::] := 0;
      responses_size' (cons hd tl) := responses_size hd + responses_size' tl
    }.


  Lemma in_responses_leq r rs :
    r \in rs -> response_size r <= responses_size rs.
  Proof.
    elim: rs => //= hd tl IH; rewrite inE => /orP [/eqP -> | Hin].
      by ssromega.
      by move: (IH Hin) => Hlt; ssromega.
  Qed.

  Lemma in_responses'_leq r rs :
     r \in rs -> responses_size r <= responses_size' rs.
  Proof.
    elim: rs => // hd tl IH; rewrite inE => /orP [/eqP -> | Hin]; rewrite responses_size'_equation_2.
      by ssromega.
      by move: (IH Hin) => Hlt; ssromega.
  Qed.
  
  Lemma responses_size_app (l1 l2 : seq.seq (@ResponseObject Name Vals)) : responses_size (l1 ++ l2) = responses_size l1 + responses_size l2.
  Proof. 
    elim: l1 => [//| n l' IH].
    by simpl; rewrite IH addnA.
  Qed.
  
  

  
  Lemma response_size_n_0 (r : @ResponseObject Name Vals) : 0 < response_size r.
  Proof. by case: r. Qed.

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

  
  Definition partial_response_eq (r1 r2 : @ResponseObject Name Vals) : bool :=
    match r1, r2 with
    | (SingleResult l v), (SingleResult l' v') => (l == l') && (v == v')
    | (ListResult l v), (ListResult l' v') => (l == l') && (v == v')
    | (Null l), (Null l') => l == l'
    | (NestedResult l _), (NestedResult l' _) => l == l' 
    | (NestedListResult l _), (NestedListResult l' _) => l == l'   
    | _, _ => false
    end.

  Lemma partial_response_eqC :
    commutative partial_response_eq.
  Proof.
    case=> [l | l v | l vs | l ρ | l ρs];
    case=> [l' | l' v' | l' vs' | l' χ | l' χ] //=;
    case: eqP => [-> /= |].
    case: eqP => [-> /= |].
    do ? case eqP => //.
    by case: eqP => //=; case: eqP => // ->.
  Admitted.


    
   Lemma partial_response_eq_trans r1 r2 r3 :
    ~~partial_response_eq r1 r2 ->
    ~~partial_response_eq r2 r3 ->
    ~~partial_response_eq r1 r3.
   Proof.
     Admitted.


   Equations is_non_redundant__ρ response : bool :=
     {
       is_non_redundant__ρ (NestedResult _ ρ)  := are_non_redundant__ρ ρ;
       is_non_redundant__ρ (NestedListResult _ ρs) := all are_non_redundant__ρ ρs;
       is_non_redundant__ρ _ := true                 
     }
   where
   are_non_redundant__ρ (responses : seq (@ResponseObject Name Vals)) : bool :=
     {
       are_non_redundant__ρ [::] := true;
       are_non_redundant__ρ (hd :: tl) :=
         [&& all (fun r => r.(rname) != hd.(rname)) tl,
          is_non_redundant__ρ hd &
          are_non_redundant__ρ tl]
           
     }.

   
   Lemma are_non_redundant__ρ_uniq s :
     are_non_redundant__ρ s -> uniq s.
   Proof.
     elim: s => //= hd tl IH /and3P [Hall Hnr Hnrs].
     apply/andP; split; last by apply: IH.
     apply/memPn => y Hin.
     move/allP: Hall => /(_ y Hin) {Hin Hnr}.
     case: eqP => //= Heq _.
     case: y Heq => //= [l | l v | l vs | l ρ | l ρs];
                     case: hd => //= l'.
     by case: eqP => //; case=> ->.
     all: do [by move=> x; case: eqP => //; case=> ->].
   Qed.


   Equations have_compatible_shapes (r1 r2 : @ResponseObject Name Vals) : bool
     by wf (response_size r1) :=
     {
       have_compatible_shapes (Null _) (Null _) := true;
       have_compatible_shapes (Null l) r2 := l != r2.(rname);
       
       have_compatible_shapes (SingleResult _ _) (SingleResult _ _) := true;
       have_compatible_shapes (SingleResult l _) r2 := l != r2.(rname);
       
       have_compatible_shapes (ListResult _ _) (ListResult _ _) := true;
       have_compatible_shapes (ListResult l _) r2 := l != r2.(rname);
       
       have_compatible_shapes (NestedResult l ρ) (NestedResult l' σ) :=
              (l == l') ==> all_In ρ (fun r1 Hin1 => all_In σ (fun r2 Hin2 => have_compatible_shapes r1 r2));

       have_compatible_shapes (NestedResult l _) r2 := l != r2.(rname);

       
       have_compatible_shapes (NestedListResult l ρs) (NestedListResult l' σs) :=
         (l == l') ==>
         ((size ρs == size σs) &&
         all_In (zip ρs σs) (fun rs Hin => all_In rs.1 (fun r1 Hin1 => all_In rs.2 (fun r2 Hin2 => have_compatible_shapes r1 r2))));

       have_compatible_shapes (NestedListResult l _) r2 := l != r2.(rname)
      
     }.
   Next Obligation.
     by simp response_size; move: (in_responses_leq Hin1) => Hleq; ssromega.
   Qed.
   Next Obligation.
     simp response_size.
     move: (in_zip Hin) => {Hin} [Hin _].
     move: (in_responses_leq Hin1) => Hleq.
     move: (in_responses'_leq Hin) => Hleq'.
     by ssromega.
   Qed.

   (*
   Definition have_same_shape (r1 r2 : @ResponseObject Name Vals) : bool :=
     match r1, r2 with
     | Null _, Null _
     | SingleResult _ _, SingleResult _ _
     | ListResult _ _, ListResult _ _
     | NestedResult _ _, NestedResult _ _
     | NestedListResult _ _, NestedListResult _ _ => true
     | _, _ => false
     end.
   
   Definition have_compatible_shapes (r1 r2 : @ResponseObject Name Vals) : bool :=
     (r1.(rname) == r2.(rname)) ==> have_same_shape r1 r2.


   Lemma have_compatible_shapesP (r1 r2 : @ResponseObject Name Vals) :
     reflect (r1.(rname) != r2.(rname) \/ have_same_shape r1 r2)
             (have_compatible_shapes r1 r2).
   Proof.
     apply: (iffP idP).
     - by rewrite /have_compatible_shapes; rewrite implybE => /orP.
     - by rewrite /have_compatible_shapes => H; rewrite implybE; apply/orP.
   Qed.
   *)
   (*
   Equations have_valid_response_shape (r1 r2 : @ResponseObject Name Vals) : bool by wf (response_size r1):=
     {
       have_valid_response_shape (Null l) (Null l) := true;
       have_valid_response_shape (SingleResult l v) (SingleResult l' v') := (l == l') ==> (v == v');
       have_valid_response_shape (ListResult l vs) (ListResult l' vs') := (l == l') ==> (vs == vs');
       have_valid_response_shape (NestedResult l ρ) (NestedResult l' σ) :=
         (l == l') ==>
         all_In ρ (fun r1 Hin1 => all_In σ (fun r2 Hin2 => have_valid_response_shape r1 r2));     

       have_valid_response_shape (NestedListResult l ρs) (NestedListResult l' σs) :=
         (l == l') ==>
         ((size ρs == size σs) &&
           all_In (zip ρs σs) (fun rs Hin => all_In rs.1 (fun r1 Hin1 => all_In rs.2 (fun r2 Hin2 => have_valid_response_shape r1 r2))));

       have_valid_response_shape r1 r2 := true
     }.
   Next Obligation.
     by simp response_size; move: (in_responses_leq Hin1) => Hleq; ssromega.
   Qed.
   Next Obligation.
     simp response_size.
     move: (in_zip Hin) => {Hin} [Hin _].
     move: (in_responses_leq Hin1) => Hleq.
     move: (in_responses'_leq Hin) => Hleq'.
     by ssromega.
   Qed.
     
*)
     
   
     
   Equations(noind) wf_response response : bool :=
     {
       wf_response (NestedResult _ ρ) := wf_responses ρ;
       wf_response (NestedListResult _ ρs) := all (fun ρ => wf_responses ρ) ρs;
       wf_response _ := true
     }
   where
   wf_responses responses : bool :=
     {
       wf_responses [::] := true;
       wf_responses (hd :: tl) := [&& wf_response hd,
                                  map_all have_compatible_shapes (hd :: tl) &
                                  wf_responses tl]
     }.
   

   

   Lemma all_valid_when_no_eq r rs :
     all (fun r' => r'.(rname) != r.(rname)) rs ->
     all (have_compatible_shapes r) rs.
   Proof.
     elim: rs => //= hd tl IH /andP [/eqP Hneq Hall].
     apply/andP; split; last by apply: IH.
     case: r IH Hneq {Hall} => //= [l | l v | l vs | l ρ | l ρs] _;
     case: hd => //= l'.
     all: do ?[by intros; simp have_compatible_shapes => /=; apply/eqP => Hcontr; rewrite Hcontr in Hneq].
     all: do ?[by move=> σ Hneq; simp have_compatible_shapes => /=; case: eqP => //= Hcontr; rewrite Hcontr in Hneq].
   Qed.
     
 
   Lemma wf_responses_map_all s :
     wf_responses s -> map_all have_compatible_shapes s.
   Proof.
     by elim: s => //= hd tl IH /and3P [_].
   Qed.
   
   Lemma is_non_redundant_wf response :
     is_non_redundant__ρ response ->
     wf_response response.
   Proof.
     elim response using ResponseObject_ind with
         (Pl := fun rs =>
                 are_non_redundant__ρ rs ->
                 wf_responses rs)
         (Pl2 := fun rs =>
                  all are_non_redundant__ρ rs ->
                  all wf_responses rs).

     all: do ?[by intros; simp is_non_redundant__ρ].

     - move=> hd IHhd tl IHtl /and3P [Hall Hnr Hnrs].
       apply/and3P; split; [by apply: IHhd | | by apply: IHtl].
       simpl.
       apply/andP; split.
       by apply: all_valid_when_no_eq.
       by apply: wf_responses_map_all; apply: IHtl.
     - move=> hd IHhd tl IHtl /= /andP [Hnrs Hall].
       by apply/andP; split; [apply: IHhd | apply: IHtl].
   Qed.
     
   Lemma non_redundant_are_wf responses :
     are_non_redundant__ρ responses ->
     wf_responses responses.
   Proof.
     elim: responses => //= hd tl IH /and3P [Hall Hnr Hnrs].
     apply/and3P; split=> //; last by apply: IH.
       by apply: is_non_redundant_wf.
       apply/andP; split; last first.
       by apply: wf_responses_map_all; apply: IH.
       by apply: all_valid_when_no_eq.  
   Qed.   
     
End QueryAux.


Arguments partial_query_eq [Name Vals].
Arguments response_size [Name Vals].
Arguments is_field [Name Vals].
Arguments is_inline_fragment [Name Vals].
Arguments have_compatible_shapes [Name Vals].
Arguments wf_response [Name Vals].

