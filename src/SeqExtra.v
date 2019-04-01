

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Equations Require Import Equations.


  Lemma filter_preserves_pred T (p pred : T -> bool) (s : seq T) :
    all p s ->
    all p [seq x <- s | pred x].
  Proof.
    elim: s => [//| x s' IH] /=.
    move/andP=> [Hpx Hall].
    case (pred x) => //=.
      by move/IH: Hall => Hall; apply/andP.
      by apply: IH.
  Qed.
  
  Lemma filter_all_predC1 (T : eqType) (s : seq T) (x : T) :
    [seq x' <- s | predC1 x x'] = [::] ->
    forall x', x' \in s -> x' = x.
    elim: s x => [//| n s' IH] x /=.
    case: ifP => //.
    case: eqP => // -> _ /IH H.
    by move=> x'; rewrite in_cons => /orP [/eqP ->|]; [|apply: H]. 
  Qed.

  
  Lemma not_nil_spread {A : eqType} (lst : seq A) : lst != [::] -> exists x lst', lst = x :: lst'.
  Proof.
      by case: lst => // x lst' H; exists x; exists lst'.  Qed.

  

  Lemma ohead_in (A : eqType) (lst : seq A) (v : A) :
    ohead lst = Some v ->
    v \in lst.
  Proof.
    elim: lst => // x lst' IH /=.
      by case=> ->; rewrite inE; apply/orP; left.
  Qed.

  

  Lemma ohead_cons (A : eqType) H (x : A) lst :
    ohead (x :: lst) = H -> Some x = H.
  Proof. done. Qed.


  

  Lemma map_fs {A B C : eqType} (lst : seq A) (f : A -> B -> C) (x y : B):
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
  Admitted.

  

  Lemma singleton (A : Type) (x y : A) : x = y -> [:: x] = [:: y]. Proof. by move=> ->. Qed.


    


    Fixpoint onth {T : Type} (s : seq T) (i : nat) : option T :=
      match s, i with
      | [::], _ => None
      | (hd :: tl), 0 => Some hd
      | (hd :: tl), n.+1 => onth tl n
      end.


    