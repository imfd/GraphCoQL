From mathcomp Require Import all_ssreflect.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.







(* Section BooleanTactics. *)

Ltac orL := apply/orP; left.
Ltac orR := apply/orP; right.
 
Ltac apply_andP := apply/andP; split=> //.
Ltac apply_and3P := apply/and3P; split=> //.
  
Ltac bcase :=
  repeat match goal with
         | [|- is_true (~~ (_ || _)) -> _] => rewrite negb_or
                                                  
         | [|- is_true (_ && (_ && _)) -> _] =>
           let Hb1 := fresh "Hb1" in
           let Hb2 := fresh "Hb2" in
           let Hb3 := fresh "Hb3" in
           
           case/and3P=> [Hb1 Hb2 Hb3]
         | [|- is_true (_ && _) -> _] =>
           let Hb1 := fresh "Hb1" in
           let Hb2 := fresh "Hb2" in
           case/andP=> [Hb1 Hb2]
                        
         end.
  

(* End BooleanTactics. *)