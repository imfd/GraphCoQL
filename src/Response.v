(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import SeqExtra.


Notation Name := string.

(* end hide *)
(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Response</h1>
        <p class="lead">
         This file contains the basic building blocks to define a GraphQL Response.
        </p>
         
  </div>
</div>#
 *)

Section Response.

  (* Unsetting because the automatically generated induction principle is not good enough. *)
  Unset Elimination Schemes.

  Variable (Scalar : eqType).
  
  (** * Response
      ----
      Here we define a general Response structure, which is in essence a JSON tree.
      We later use this definition to build a GraphQL Response.     

      A response can be either:
      - an optional _scalar_ values (to account for null values),
      - an object, mapping keys to other responses, or
      - an array of response values.
   *)
  Inductive ResponseValue : Type :=
  | Leaf : option Scalar -> ResponseValue
  | Object : seq (Name * ResponseValue) -> ResponseValue
  | Array : seq ResponseValue -> ResponseValue.
  
  Set Elimination Schemes.

  
  (** * GraphQL Response 
      ----      
      
      A GraphQL Response is, in essence, a JSON Object, mapping keys 
      to other response values.
   *)  
  Definition GraphQLResponse := seq (Name * ResponseValue).

  

  (** We define some auxiliary definitions *)
  (** ---- *)
  (**
     Gets the size of the response tree.
   *)
  
  Equations rsize (response : ResponseValue) : nat :=
    {
      rsize (Leaf _) := 1;
      rsize (Object rt) := (lrsize rt).+1;
      rsize (Array rt) := (list_size rsize rt).+1
    }
  where lrsize (r : seq (Name * ResponseValue)) : nat :=
          {
            lrsize [::] := 0;
            lrsize (hd :: tl) := rsize hd.2 + lrsize tl
          }.
  

  (** ---- *)
  (**
     This predicate checks whether the responses are non-redundant.
     
     Non-redundancy means that there are no duplicated keys.
   *)
  
  Equations is_non_redundant (response : ResponseValue) : bool :=
          {
            is_non_redundant (Leaf _) := true;

            is_non_redundant (Object rt) := are_non_redundant rt;

            is_non_redundant (Array rt) := all is_non_redundant rt
          }
  where are_non_redundant (responses : seq (Name * ResponseValue)) : bool  :=
    {
      are_non_redundant [::] := true;

      are_non_redundant ((k, q) :: qs) := [&& is_non_redundant q,
                                          all (fun kq => kq.1 != k) qs &
                                          are_non_redundant qs]
    }.
  
  
  
End Response.

(* begin hide *)
Arguments ResponseValue [Scalar].
Arguments Leaf [Scalar].
Arguments Object [Scalar].
Arguments Array [Scalar].
Arguments is_non_redundant [Scalar].
Arguments are_non_redundant [Scalar].
(* end hide *)

Delimit Scope response_scope with RESP.
Open Scope response_scope.

Notation "{- ρ -}" := (Object ρ) : response_scope.


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Query.html' class="btn btn-light" role='button'>Previous ← Query</a>
        <a href='GraphCoQL.QuerySemantics.html' class="btn btn-info" role='button'>Continue Reading → Query Semantics</a>
    </div>#
*)

  
  