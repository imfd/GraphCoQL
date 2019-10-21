
From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

Require Import SchemaAux.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import Ssromega.






  (**
     This tactic tries to solve statements that involve inequalities with 
     queries sizes.
   *)
  Ltac leq_selections_size :=
    repeat match goal with
           | [|- context [ selection_size _]] => simp selection_size => /=
           | [|- context[ (_ < selections_size_aux (_ :: _))%coq_nat] ] =>
             rewrite {2}/selections_size_aux /= -/(selections_size_aux _); simp selection_size

           | [|- context [selections_size_aux [seq (_, σ) | σ <- ?σs] ] ] =>
     rewrite [selections_size_aux [seq _ | _ <- _] ]/selections_size_aux /= -map_comp /funcomp map_id

           | [|- context [ selections_size_aux (_ ++ _) ]] => rewrite selections_size_aux_cat /=
           | [|- context [ selections_size (_ ++ _)]] => rewrite selections_size_cat

           | [|- context [ selections_size (merge_selection_sets (find_valid_fields_with_response_name ?s ?rname ?ty ?qs)) ]] =>
             let Hfleq := fresh in
             let Hmleq := fresh in
             have Hfleq := (found_queries_leq_size s rname ty qs);
             have Hmleq := (merged_selections_leq (find_valid_fields_with_response_name s rname ty qs)); ssromega                         

           | [|- context [selections_size_aux (merge_pairs_selection_sets ?s (find_valid_pairs_with_response_name ?s ?ts ?rname ?qs)) ]] =>
             let Hfleq := fresh in
             let Hmleq := fresh in
             have Hfleq := (found_valid_pairs_leq_size s ts rname qs);
             have Hmleq := (merge_pair_selections_leq s (find_valid_pairs_with_response_name s ts rname qs)); ssromega
                                                                                                                          
           | [|- context [ selections_size (merge_selection_sets (find_fields_with_response_name ?rname ?qs)) ]] =>
              let Hfleq := fresh in
              let Hmleq := fresh in
              have Hfleq := (found_fields_leq_size rname qs);
              have Hmleq := (merged_selections_leq (find_fields_with_response_name rname qs)); ssromega
                                                                                                             
            | [|- context [selections_size_aux (merge_pairs_selection_sets ?s (find_pairs_with_response_name ?rname ?qs)) ] ] =>
             let Hfleq := fresh in
             let Hmleq := fresh in
             have Hfleq := (found_pairs_with_response_name_leq rname qs);
             have Hmleq := (merge_pair_selections_leq s (find_pairs_with_response_name rname qs)); ssromega
                                                                                               
           | [|- context [selections_size (merge_selection_sets ?qs)]] =>
              let Hfleq := fresh in
              have Hfleq := (merged_selections_leq qs); ssromega                            

           | [|- context [selections_size_aux (filter_pairs_with_response_name ?rname ?σs)] ] =>
             let Hfleq := fresh in
             have Hfleq := (filter_pairs_with_response_name_leq rname σs); ssromega
                      
           | [|- context [selections_size (filter_queries_with_label ?rname ?qs)]] =>
             let Hfleq := fresh in
             have Hfleq := (filter_queries_with_label_leq_size rname qs); ssromega

           | [|- context [selections_size (filter_queries_with_label ?rname1 ?qs1) +
                         selections_size (filter_queries_with_label ?rname2 ?qs2)]] =>
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
                                                   case Hlook : lookup_field_in_type => [fld|] //=
    end.