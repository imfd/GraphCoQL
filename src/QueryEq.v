From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord.

Require Import Schema.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import Graph.
Require Import GraphConformance.
Require Import QueryConformance.
Require Import QuerySemantic.
Require Import NRGTNF.

Section Eq.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

    Inductive QueryEquiv schema : conformedQuery schema -> conformedQuery schema -> Prop :=
    | QEq : forall q1 q2,
        forall (g : @conformedGraph N Name Vals schema),
          eval_selection g q1 = eval_selection g q2 ->
        QueryEquiv q1 q2.


    Theorem all_q_has_nrgtnf_q schema : forall (q : conformedQuery schema), exists (q' : normalizedSelection),
    	  QueryEquiv q q'.
    Proof. Admitted.


    Lemma nrgtnf_q_eval_same schema :
      forall (ϕ : normalizedSelection),
        selection_conforms schema ϕ schema.(query_type) ->
        forall (g : @conformedGraph N Name Vals schema),
          eval schema g.(graph) g.(graph).(root) ϕ = eval' schema g.(graph) g.(graph).(root) ϕ.

    Proof.
      case=> s H1 H2 /=.ta
              
    
End Eq.