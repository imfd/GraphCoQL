

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Equations Require Import Equations.


Section SeqExtra.

  Variables (A B C : eqType) (T : Type).
  
  Lemma filter_preserves_pred (p pred : A -> bool) (s : seq A) :
    all p s ->
    all p [seq x <- s | pred x].
  Proof.
    elim: s => [//| x s' IH] /=.
    move/andP=> [Hpx Hall].
    case (pred x) => //=.
      by move/IH: Hall => Hall; apply/andP.
      by apply: IH.
  Qed.
  
  Lemma filter_all_predC1 (s : seq A) (x : A) :
    [seq x' <- s | predC1 x x'] = [::] ->
    forall x', x' \in s -> x' = x.
    elim: s x => [//| n s' IH] x /=.
    case: ifP => //.
    case: eqP => // -> _ /IH H.
    by move=> x'; rewrite in_cons => /orP [/eqP ->|]; [|apply: H]. 
  Qed.

  
  Lemma not_nil_spread (lst : seq A) : lst != [::] -> exists x lst', lst = x :: lst'.
  Proof.
      by case: lst => // x lst' H; exists x; exists lst'.  Qed.

  

  Lemma ohead_in (lst : seq A) (v : A) :
    ohead lst = Some v ->
    v \in lst.
  Proof.
    elim: lst => // x lst' IH /=.
      by case=> ->; rewrite inE; apply/orP; left.
  Qed.

  

  Lemma ohead_cons H (x : A) lst :
    ohead (x :: lst) = H -> Some x = H.
  Proof. done. Qed.


  

  Lemma map_fs (lst : seq A) (f : A -> B -> C) (x y : B):
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
  Abort.
  

  Lemma singleton (x y : A) : x = y -> [:: x] = [:: y]. Proof. by move=> ->. Qed.    


  Fixpoint onth (s : seq T) (i : nat) : option T :=
    match s, i with
    | [::], _ => None
    | (hd :: tl), 0 => Some hd
    | (hd :: tl), n.+1 => onth tl n
    end.



 
  
End SeqExtra.

Section SeqI.
  Variable (A : eqType).
  
  Definition seqI (s1 s2 : seq A) :=
    undup (filter (mem s1) s2).
  
  Notation "s1 :&: s2" := (seqI s1 s2) : seq_scope.

  Open Scope SEQ.

  Lemma in_seqI (x : A) s1 s2 :
    x \in (s1 :&: s2) = (x \in s1) && (x \in s2).
  Proof.
    by rewrite /seqI mem_undup mem_filter.
  Qed.

  Lemma seq1I (x : A) s1 :
    [:: x] :&: s1 = if x \in s1 then [:: x] else [::].
  Proof.
    rewrite /seqI fun_if.
    case: ifP => //= Hin; last first.
  Admitted.
    
  Lemma seq1I_N_nil (x : A) s1 :
    [:: x] :&: s1 != [::] -> x \in s1.
  Proof.
    by rewrite seq1I; case: ifP.
  Qed.

  Lemma seq1IC x s1 :
    [:: x] :&: s1 = s1 :&: [:: x].
  Proof.
    rewrite {2}/seqI /= seq1I.
    by case: ifP.
  Qed.
    
End SeqI.

Notation "s1 :&: s2" := (seqI s1 s2) : seq_scope.


Arguments seqI [A].

  