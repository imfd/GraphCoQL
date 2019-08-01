

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Equations Require Import Equations.

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

  
  Lemma get_firstP  (p : pred A) (s : seq A) : reflect (exists2 x, x \in s & p x) (get_first p s).
  Proof.
    apply: (iffP idP).
    - elim: s => // hd tl IH.
      rewrite /get_first.
      case: ifP => //.
      * by exists hd => //; apply mem_head.
             * by move=> _ /IH; case=> [x Hin Hp]; exists x => //; rewrite in_cons; apply/orP; right.     
             - case=> x Hin Hp.
               rewrite /get_first.
               elim: s Hin => // hd tl IH.
               rewrite in_cons => /orP [/eqP <- | Htl].
                 by rewrite Hp.
                 case: ifP => // _.
                   by apply: IH.
  Qed.



  
  Lemma get_first_E (p : pred A) s tdef : (get_first p s = Some tdef) -> get_first p s.
  Proof.
      by move=> ->.
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

  Fixpoint map_all (p : A -> A -> bool) (s : seq A) : bool :=
    match s with
    | [::] => true
    | (hd :: tl) => all (p hd) tl && map_all p tl
    end.

  Lemma map_all_cat_2 p s1 s2 :
    map_all p (s1 ++ s2) -> map_all p s2.
  Proof.
    elim: s1 => //= hd tl IH /andP [_].
      by apply: IH.
  Qed.
  
  Lemma mem_tail s (x hd : A) : x \in s -> x \in (hd :: s).
  Proof.
      by rewrite in_cons => Hin; apply/orP; right.
  Qed.

  
  Lemma filter_preserves_map_all (p : A -> A -> bool) (pred : A -> bool) (s : seq A) :
    map_all p s ->
    map_all p [seq x <- s | pred x].
  Proof.
    elim: s => [//| x s' IH] /=.
    move/andP=> [Hpx Hall].
    case (pred x) => //=.
    apply/andP; split=> //.
      by apply: filter_preserves_pred.
      all: do [by apply: IH].
  Qed.
  
  Lemma in_zip (x1 x2 : A) s1 s2 : (x1, x2) \in zip s1 s2 ->
                                                x1 \in s1 /\ x2 \in s2.
  Proof.
    elim: s1 s2 => //= [| hd tl IH] s2.
    - by case: s2.
    - case: s2 => //= hd2 tl2 Hin.
      rewrite inE in Hin.
      move/orP: Hin => [/eqP | Htl].
      * by case=> -> ->; split; apply: mem_head.
      * move: (IH tl2 Htl) => [Htl1 Htl2].
          by split; apply: mem_tail.
  Qed.
  
End SeqExtra.

Unset Implicit Arguments.

Section All.
  
  Equations all_In {A : eqType} (s : seq A) (f : forall x, x \in s -> bool) : bool :=
    {
      all_In [::] _ := true;
      all_In (hd :: tl) f := (f hd _) && (all_In tl (fun x H => f x _))
    }.
  Next Obligation.
      by apply: mem_head.
  Qed.
  Next Obligation.
      by apply: mem_tail.
  Qed.

  Lemma all_In_eq_all {A : eqType} (s : seq A) (f : A -> bool) :
    all_In s (fun x _ => f x) = all f s.
  Proof.
      by elim: s => //= hd tl IH; simp all_In; rewrite IH.
  Qed.
  

End All.

Section Map.
  Variables (A : eqType) (B : Type).
  
  Equations? map_in (l : seq A) (f : forall (x : A), x \in l -> B) : seq B :=
    {
      map_in nil _ := nil;
      map_in (cons x xs) f := cons (f x _) (map_in xs (fun x H => f x _))
    }.
    by apply: mem_head.
      by apply: mem_tail.
  Qed.

  Lemma map_in_eq (s : seq A) (f : A -> B) :
    map_in s (fun x _ => f x) = map f s.
  Proof.
      by elim: s => //= hd tl IH; simp map_in; rewrite IH.
  Qed.
  
End Map.


Set Implicit Arguments.

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

Section Max.
  Variable (A B : Type).

  Fixpoint seq_max (s : seq nat) := foldr max 0 s.

  Fixpoint seq_fmax (f : A -> nat) (s : seq A) : nat :=
    match s with
    | [::] => 0
    | x :: xs => max (f x) (seq_fmax f xs)
    end.

  Lemma seq_fmax_cat (f : A -> nat) (s1 s2 : seq A) :
    seq_fmax f (s1 ++ s2) = max (seq_fmax f s1) (seq_fmax f s2).
  Proof.
    elim: s1 => //= x s1 IH.
      by rewrite -Nat.max_assoc /= IH.
  Qed.

  
End Max.


Section list_size.
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
    list_size nil := 0;
                      list_size (cons x xs) := S (f x + list_size xs).

  
End list_size.


 Lemma seq0Pn (A : eqType) (s : seq A) : reflect (exists x, x \in s) (s != [::]).
    Proof.
      apply: (iffP idP) => //.
      - by case: s => // hd tl _; exists hd; apply: mem_head.
      - by case: s => //; case=> [x]; rewrite in_nil.
    Qed.
    
  


    Lemma in_N_nilP {A : eqType} (s : seq A) : reflect (exists x, x \in s) (s != [::]).
    Proof.
      apply: (iffP idP) => //.
        by case: s => // a *; exists a; rewrite inE; apply/orP; left. 
          by case: s => //; case=> [x]; rewrite in_nil.
    Qed.

    
Notation "s1 :&: s2" := (seqI s1 s2) : seq_scope.


Arguments seqI [A].

Arguments map_in [A B].
