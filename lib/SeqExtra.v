(* begin hide *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Arith.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Seq Extra</h1>
        <p class="lead">
         This file contains some basic lemmas over seq and extra definitions used in the project.
        </p>         
  </div>
</div>#
 *)

Section SeqExtra.

  Variables (A B C : eqType) (T : Type).

  (** ---- *)
  (**
     #<strong>get_first</strong># : (A → Bool) → seq A → option A

     Gets the first element in the list that satisfies the predicate.
   *)
  Fixpoint get_first p (lst : seq A) :=
    if lst is hd :: tl then
      if p hd then
        Some hd
      else
        get_first p tl
    else
      None.

  (** ---- *)
  (**
     This lemma states that the first element obtained by [get_first] satisfies
     the predicate.
   *)
  Lemma get_first_pred (p : pred A) (s : seq A) (x : A) :
    get_first p s = Some x ->
    p x.
  Proof.
      by elim: s => //= y s IH; case: ifP => //= Hp; case=> <-.
  Qed.


  (** ---- **)
  (**
     This lemma states that an element belongs both to a list and the 
     same list without duplicates.
   *)
  Lemma in_undup (s : seq A) (x : A) :
    x \in s <-> x \in undup s.
  Proof.
    elim: s => //= y s [IHl IHr]; split.
    - rewrite inE => /orP [/eqP <- | Hin]; case: ifP => //=.
      * by intros; apply/orP; left; apply/eqP.
      * by intros; apply: IHl.
      * by intros; apply/orP; right; apply: IHl.
    - case: ifP => //=; intros; rewrite inE; apply/orP.
      * by right; apply: IHr.
      * by case/orP: H => [/eqP <- | Hin]; [left; apply/eqP | right; apply: IHr].      
  Qed.

  
  (** ---- **)
  (**
     This lemma states that if [ohead] returns an element [v]
     then that element belongs to the list.
   *)
  Lemma ohead_in (lst : seq A) (v : A) :
    ohead lst = Some v ->
    v \in lst.
  Proof.
    elim: lst => // x lst' IH /=.
      by case=> ->; rewrite inE; apply/orP; left.
  Qed.
 
  (** ---- **)
  (**
     This lemma states that if a list belongs to a list then
     it belongs to the tail of the cons (similar to [mem_head]).
   *)
  Lemma mem_tail s (x hd : A) : x \in s -> x \in (hd :: s).
  Proof.
      by rewrite in_cons => Hin; apply/orP; right.
  Qed.

  
  
End SeqExtra.



Set Implicit Arguments.

Section SeqI.
  Variable (A : eqType).

  (** ---- *)
  (**
     #<strong></strong>#: seq A → seq A → seq A

     Intersects two lists.

     This is used in [is_fragment_spread_possible].
   *)
  Definition seqI (s1 s2 : seq A) :=
    undup (filter (fun s => s \in s1) s2).
  
  Infix ":&:" := seqI : seq_scope.

  Open Scope SEQ.

  (** ---- **)
  (**
     This lemma states that an element in the intersection of two lists 
     belongs to each individually.
   *)
  Lemma in_seqI (x : A) s1 s2 :
    x \in (s1 :&: s2) = (x \in s1) && (x \in s2).
  Proof.
      by rewrite /seqI mem_undup mem_filter.
  Qed.

  (** ---- **)
  (**
     This lemma states that the intersection of a singleton list 
     to any other list results in either the same singleton list or 
     an empty list.
   *)
  Lemma seq1I (x : A) s :
    [:: x] :&: s = if x \in s then [:: x] else [::] .
  Proof.
    rewrite /seqI.
    elim: s => //= s1 s IH.
    case: ifP.
    - rewrite mem_seq1 => /eqP Heq.
      rewrite Heq in IH *; rewrite mem_head /= mem_filter mem_head /=.
        by case: ifP => // Hin; rewrite Hin in IH; rewrite IH.
    - rewrite mem_seq1 => Hneq.
        by rewrite inE eq_sym Hneq /= IH.
  Qed.

  (* These lemmas are repeated... It should suffice to prove
     commutativity of the intersection, but for some reason I cannot do it --
     my mind is not on the mood apparently 
   *)

  (** ---- **)
  (**
     This lemma states that if an element [x] is in a list, then 
     intersecting it to the list returns the same element.
   *)
  Lemma mem_seqI1 (x : A) s1 :
    x \in s1 <->
          s1 :&: [:: x] = [:: x].
  Proof.
    split.
    - by rewrite /seqI /= => ->.
    - by rewrite /seqI /=; case: ifP.
  Qed.

  (** ---- **)
  (**
     This lemma states that if an element [x] is in a list, then 
     intersecting it to the list returns the same element.
   *)
  Lemma mem_seq1I (x : A) s1 :
    x \in s1 <->
          [:: x] :&: s1 = [:: x].
  Proof.
      by rewrite seq1I; case: ifP.
  Qed.

  (** ---- **)
  (**
     This lemma states that if the intersection of a list with a singleton list 
     is not empty then the intersection must be that singleton list.
   *)
  Lemma seqI1_Nnil s1 x :
    s1 :&: [:: x] != [::] <->
    s1 :&: [:: x] = [:: x].
  Proof.
    elim: s1 => //= x1 s1 IH.
    rewrite /seqI /=.
      by case: ifP.
  Qed.

  (** ---- *)
  (**
     This lemma states that if the intersection of a list with a singleton list 
     is not empty then the intersection must be that singleton list.
   *)
  Lemma seq1I_Nnil s x :
    [:: x] :&: s != [::] <->
    [:: x] :&: s = [:: x].
  Proof.
    elim: s => //= x1 s IH.
    rewrite seq1I.
      by case: ifP.
  Qed.
  
End SeqI.


Section Cat.
  Variable (A : Type).

  (** ---- **)
  (**
     This lemma states that if a concatenation of two lists is empty 
     then both lists are empty.
   *)
  Lemma cat_nil (s1 s2 : seq A) :
    s1 ++ s2 = [::] ->
    s1 = [::] /\ s2 = [::].
  Proof.
      by case: s1.
  Qed.
  
End Cat.

Section list_size.
  Context {A : Type} (f : A -> nat).

  (** ---- *)
  (**
     #<strong>list_size</strong>#: (A → Nat) → seq A → Nat

     Calculates the size of the list based on the length of the list plus 
     the result of applying an auxiliary function.
   *)
  Fixpoint list_size (l : list A) : nat :=
    match l with
    | [::] => 0
    | x :: xs => (f x + list_size xs).+1
    end.

  
End list_size.

Notation "s1 :&: s2" := (seqI s1 s2) : seq_scope.



