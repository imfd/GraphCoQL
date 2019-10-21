(* begin hide *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* end hide *)


(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">String</h1>
        <p class="lead">
         This file is only intended to establish that the string datatype has 
         a decidable procedure for equality (and therefore in eqType).
        </p>         
  </div>
</div>#
 *)

Require Import String.

Section Equality.

  (** Since the newest version of Coq includes basically the same thing, we can simply use it directly.  *)
  Canonical string_eqType := EqType string (EqMixin eqb_spec).

  (* Another option is to use something like what Arthur Azevedo does in CoqUtils.

     https://github.com/arthuraa/coq-utils/blob/master/theories/string.v

     With it, you can establish more properties on strings (choice, count), but
     we don't really need them, so I'm not including them for now.
   *)
  

End Equality.