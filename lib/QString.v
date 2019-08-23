From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String Ascii.

Section Equality.

  (* For some reason my Coq version does not contain the equality procedures 
     for ASCII and String - Maybe they were included in version 8.8.9?
     (https://github.com/coq/coq/commit/a697b20f5013abb834cd9dca3fdef2bee53221ad#diff-ed3d66bdeac09ee75e1f7ef847000be4). 
     
     For now I am just taking their definition...

     They actually have the proof that their procedure reflects to equality (=), 
     as in Ssreflect... so... Not sure what to do.

     Anyway, in the meanwhile (before updating my version of Coq). I will 
     use what Arthur Azevedo did in CoqUtils.

     https://github.com/arthuraa/coq-utils/blob/master/theories/string.v

     I am not directly using his library because he requires a lot more than 
     what I need for the moment (ordType).
   *)
  
  Definition tuple_of_ascii c :=
    let: Ascii x1 x2 x3 x4 x5 x6 x7 x8 := c in
    (x1, x2, x3, x4, x5, x6, x7, x8).
  
  Definition ascii_of_tuple t :=
    let: (x1, x2, x3, x4, x5, x6, x7, x8) := t in
    Ascii x1 x2 x3 x4 x5 x6 x7 x8.

  Lemma tuple_of_asciiK : cancel tuple_of_ascii ascii_of_tuple.
  Proof. by case. Qed.

  Canonical ascii_eqType := EqType ascii (CanEqMixin tuple_of_asciiK).
  Canonical ascii_choiceType := ChoiceType ascii (CanChoiceMixin tuple_of_asciiK).
  Canonical ascii_countEqType := CountType ascii (CanCountMixin tuple_of_asciiK).


  
  Fixpoint seq_of_string s :=
    if s is String c s' then c :: seq_of_string s'
    else [::].

  Fixpoint string_of_seq s :=
    if s is c :: s' then String c (string_of_seq s')
    else EmptyString.

  Lemma seq_of_stringK : cancel seq_of_string string_of_seq.
  Proof. by elim=> [|c s /= ->]. Qed.
  
  Canonical string_eqType := EqType string (CanEqMixin seq_of_stringK).
  Canonical string_choiceType := ChoiceType string (CanChoiceMixin seq_of_stringK).
  Canonical string_countType := CountType string (CanCountMixin seq_of_stringK).

End Equality.