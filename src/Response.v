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


Section Response.

  Variable (A : Type).
  
  Unset Elimination Schemes.

  Inductive ResponseNode : Type :=
  | Leaf : A -> ResponseNode
  | Object : seq (Name * ResponseNode) -> ResponseNode
  | Array : seq ResponseNode -> ResponseNode.

  
  Set Elimination Schemes.


  Definition is_leaf (rnode : ResponseNode) : bool :=
      if rnode is Leaf _ then true else false.

  Definition is_object (rnode : ResponseNode) : bool :=
      if rnode is Object _ then true else false.

  Definition is_array (rnode : ResponseNode) : bool :=
    if rnode is Array _ then true else false.


  Equations rsize (response : ResponseNode) : nat :=
    {
      rsize (Leaf _) := 1;
      rsize (Object rt) := (lrsize rt).+1;
      rsize (Array rt) := (list_size rsize rt).+1
    }
  where lrsize (r : seq (Name * ResponseNode)) : nat :=
          {
            lrsize [::] := 0;
            lrsize (hd :: tl) := rsize hd.2 + lrsize tl
          }.
  

  Equations is_non_redundant (response : ResponseNode) : bool :=
          {
            is_non_redundant (Leaf _) := true;

            is_non_redundant (Object rt) := are_non_redundant rt;

            is_non_redundant (Array rt) := all is_non_redundant rt
          }
  where are_non_redundant (responses : seq (Name * ResponseNode)) : bool  :=
    {
      are_non_redundant [::] := true;

      are_non_redundant ((k, q) :: qs) := [&& is_non_redundant q,
                                          all (fun kq => kq.1 != k) qs &
                                          are_non_redundant qs]
    }.
  
  
  
    
End Response.


Section GraphQLResponse.
  
  Variable (Vals : eqType).
  
  Definition GraphQLResponse := seq (Name * (@ResponseNode (option Vals))).

End GraphQLResponse.

Arguments ResponseNode [A].
Arguments Leaf [A].
Arguments Object [A].
Arguments Array [A].


Delimit Scope response_scope with RESP.
Open Scope response_scope.

Notation "{- ρ -}" := (Object ρ) : response_scope.
  
  