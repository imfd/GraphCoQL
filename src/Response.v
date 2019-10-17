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

  
  Unset Elimination Schemes.

  Variable (Scalar : eqType).
  
  (** * Response *)
  (** ---- *)
  (**
     Here we define a general Response structure, which is in essence a JSON tree.
     We later use this definition to build a GraphQL Response.     

     There are:
     - Leaf nodes: Contain _scalar_ values.
     - Object nodes: Contain key-value elements.
     - Array nodes: Contain elements
   *)

  Inductive ResponseValue : Type :=
  | Leaf : option Scalar -> ResponseValue
  | Object : seq (Name * ResponseValue) -> ResponseValue
  | Array : seq ResponseValue -> ResponseValue.
  
  Set Elimination Schemes.

  
  (** * GraphQL Response 

   A GraphQL Response is in essence a JSON Object.

   *)  
  Definition GraphQLResponse := seq (Name * ResponseValue).

  

  (** ---- *)
  (**
     #<strong>rsize</strong># : ResponseValue → Nat

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
     #<strong>is_non_redundant</strong># : ResponseValue → Bool 

     This predicate checks whether the responses are non-redundant.
     
     Non-redundancy means that there are no repeated keys.
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
  
  
  
(** ---- *)    
End Response.

Arguments ResponseValue [Scalar].
Arguments Leaf [Scalar].
Arguments Object [Scalar].
Arguments Array [Scalar].
Arguments is_non_redundant [Scalar].
Arguments are_non_redundant [Scalar].


Delimit Scope response_scope with RESP.
Open Scope response_scope.

Notation "{- ρ -}" := (Object ρ) : response_scope.


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Graph.html' class="btn btn-light" role='button'> Previous ← GraphQL Graph </a>
        <a href='GraphCoQL.QuerySemantic.html' class="btn btn-info" role='button'>Continue Reading → Query Semantics</a>
    </div>#
*)

  
  