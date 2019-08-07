From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import Graph.
Require Import GraphAux.
Require Import SeqExtra.

Section Theory.
  Variables (Vals : eqType).
  Variable (graph :  @graphQLGraph Vals).
  Implicit Type edge : @node Vals * @fld Vals * @node Vals.

  

  Lemma root_in_nodes : graph.(root) \in graph.(nodes).
  Proof.
    rewrite /nodes -in_undup.
      by apply/orP; left; apply/eqP.
  Qed.

  
  Lemma neighbours_are_in_nodes u fld:
    forall x, x \in neighbours_with_field graph u fld -> x \in graph.(nodes).
  Proof.
    rewrite /neighbours_with_field /nodes => x.
    rewrite -?in_undup => /mapP [v].
    rewrite mem_filter => /andP [/andP [/eqP Hsrc /eqP Hfld] Hin] /= Heq.
    apply/orP; right.
    apply/flatten_mapP.
    exists v => //=.
    rewrite /enodes inE; apply/orP; right.
    by rewrite mem_seq1; apply/eqP.
  Qed.
   
  
    
  Lemma ohead_in_nodes nds v :
    all (fun node => node \in graph.(nodes)) nds ->
    ohead nds = Some v ->
    v \in graph.(nodes). 
  Proof.
    elim: nds => // x nds IH /=.
    by move=> H; case=> Heq; rewrite Heq in H; move/andP: H => [H _]. 
  Qed.
  
End Theory.