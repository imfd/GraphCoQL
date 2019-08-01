
From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

Require Import SchemaAux.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import Ssromega.
  
  Ltac case_query q :=
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
    
  
  Ltac kill_neq :=
    match goal with
    | [H : ?x <> ?y |- context [_ != _]] => idtac "ok"
    end.

  
  Ltac leq_queries_size :=
    repeat match goal with
           | [|- context [ query_size _]] => simp query_size => /=
           | [|- context [ queries_size (_ ++ _)]] => rewrite queries_size_cat
           | [|- context [ queries_size (merge_selection_sets (find_queries_with_label ?s ?rname ?ty ?qs)) ]] =>
             let Hfleq := fresh in
             let Hmleq := fresh in
             have Hfleq := (found_queries_leq_size s rname ty qs);
             have Hmleq := (merged_selections_leq (find_queries_with_label s rname ty qs)); ssromega                         
     
           | [|- context [queries_size (merge_selection_sets ?qs)]] =>
              let Hfleq := fresh in
              have Hfleq := (merged_selections_leq qs); ssromega                            
         
           | [|- context [queries_size (filter_queries_with_label ?rname ?qs)]] =>
             let Hfleq := fresh in
             have Hfleq := (filter_queries_with_label_leq_size rname qs); ssromega

           | [|- context [queries_size (filter_queries_with_label ?rname1 ?qs1) +
                         queries_size (filter_queries_with_label ?rname2 ?qs2)]] =>
             let Hfleq1 := fresh in
             let Hfleq2 := fresh in
             have Hfleq1 := (filter_queries_with_label_leq_size rname1 qs1);
             have Hfleq2 := (filter_queries_with_label_leq_size rname2 qs2); ssromega

         
           | [|- _] => ssromega
    end.

   Ltac lookup :=
    match goal with
    | [ |- context [ lookup_field_in_type _ _ _]] => let Hlook := fresh "Hlook" in
                                                   let fld := fresh "fld" in
                                                   case Hlook : lookup_field_in_type => //= [fld|]
    end.