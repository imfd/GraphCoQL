From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord.

Require Import Query.



Section QueryAux.

  Variables S Vals : ordType.

  Implicit Type query : @Query S Vals.
  
  Fixpoint size query : nat :=
    match query with
    | NestedField _ _ q' => 1 + (size q')
    | NestedLabeledField _ _ _ q' => 1 + (size q')
    | InlineFragment _ q' => 1 + (size q')
    | SelectionSet q' q'' => (size q') + (size q'')
    | _ => 1
    end.


  
End QueryAux.