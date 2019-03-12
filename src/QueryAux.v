From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap.

Require Import Query.

Require Import Ssromega.

Section QueryAux.

  Variables Name Vals : ordType.

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.

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
  
  (** Partial equality between queries.
      It basically ignores subqueries and only checks labels, names and arguments **)
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => (l == l') && (n == n') && (α == α')
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
  Equations(noind) response_size response : nat :=
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

 
End QueryAux.


Arguments partial_query_eq [Name Vals].
Arguments response_size [Name Vals].
Arguments is_field [Name Vals].
Arguments is_inline_fragment [Name Vals].