From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import Arith.

Section SeqExtra.

  Variables (A B C : eqType) (T : Type).

  Fixpoint get_first p (lst : seq A) :=
    if lst is hd :: tl then
      if p hd then
        Some hd
      else
        get_first p tl
    else
      None.

 

  Lemma get_first_pred (p : pred A) (s : seq A) (x : A) :
    get_first p s = Some x ->
    p x.
  Proof.
      by elim: s => //= y s IH; case: ifP => //= Hp; case=> <-.
  Qed.

  
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

  

  Lemma ohead_in (lst : seq A) (v : A) :
    ohead lst = Some v ->
    v \in lst.
  Proof.
    elim: lst => // x lst' IH /=.
      by case=> ->; rewrite inE; apply/orP; left.
  Qed.
 
  
  Lemma mem_tail s (x hd : A) : x \in s -> x \in (hd :: s).
  Proof.
      by rewrite in_cons => Hin; apply/orP; right.
  Qed.

  
  
End SeqExtra.



Set Implicit Arguments.

Section SeqI.
  Variable (A : eqType).
  
  Definition seqI (s1 s2 : seq A) :=
    undup (filter (fun s => s \in s1) s2).
  
  Infix ":&:" := seqI : seq_scope.

  Open Scope SEQ.

  Lemma in_seqI (x : A) s1 s2 :
    x \in (s1 :&: s2) = (x \in s1) && (x \in s2).
  Proof.
      by rewrite /seqI mem_undup mem_filter.
  Qed.

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
  Lemma mem_seqI1 (x : A) s1 :
    x \in s1 <->
          s1 :&: [:: x] = [:: x].
  Proof.
    split.
    - by rewrite /seqI /= => ->.
    - by rewrite /seqI /=; case: ifP.
  Qed.

  Lemma mem_seq1I (x : A) s1 :
    x \in s1 <->
          [:: x] :&: s1 = [:: x].
  Proof.
      by rewrite seq1I; case: ifP.
  Qed.

  Lemma seqI1_Nnil s1 x :
    s1 :&: [:: x] != [::] <->
    s1 :&: [:: x] = [:: x].
  Proof.
    elim: s1 => //= x1 s1 IH.
    rewrite /seqI /=.
      by case: ifP.
  Qed.

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

  Lemma cat_nil (s1 s2 : seq A) :
    s1 ++ s2 = [::] ->
    s1 = [::] /\ s2 = [::].
  Proof.
      by case: s1.
  Qed.
  
End Cat.

Section list_size.
  Context {A : Type} (f : A -> nat).

  Fixpoint list_size (l : list A) : nat :=
    match l with
    | [::] => 0
    | x :: xs => (f x + list_size xs).+1
    end.

  
End list_size.
Notation "s1 :&: s2" := (seqI s1 s2) : seq_scope.


Arguments seqI [A].

