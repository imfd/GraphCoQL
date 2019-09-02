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


  (*
  Definition ResponseTree_rect (P : forall l : L, ResponseTree l -> Type)
             (Pn : ResponseNode -> Type)
             (Pll : seq (B * ResponseNode) -> Type)
             (Pul : seq ResponseNode -> Type)
             (IH_LRTree : forall rns, Pll rns -> P Labeled (LRTree rns))
             (IH_URTree : forall rns, Pul rns -> P Unlabeled (URTree rns))
             (IH_Leaf : forall v, Pn (Leaf v))
             (IH_Object : forall rt, P Labeled rt -> Pn (Object rt))
             (IH_Array : forall rt, P Unlabeled rt -> Pn (Array rt))
             (IH_LNil : Pll [::])
             (IH_UNil : Pul [::])
             (IH_LCons : forall l rn, Pn rn -> forall rns, Pll rns -> Pll ((l, rn) :: rns))
             (IH_UCons : forall rn, Pn rn -> forall rns, Pul rns -> Pul (rn :: rns)) :=
    
    fix loop l rt : P l rt :=
      let fix Fn (rn : ResponseNode) : Pn rn :=
          match rn with
          | Leaf v => IH_Leaf v
          | Object rt => IH_Object rt (loop Labeled rt)
          | Array rt => IH_Array rt (loop Unlabeled rt)
          end
      in
      let fix Fll (rns : seq (B * ResponseNode)) : Pll rns :=
          match rns with
          | [::] => IH_LNil
          | (l, rn) :: rns' => IH_LCons l rn (Fn rn) rns' (Fll rns')
          end
      in
      let fix Ful (rns : seq ResponseNode) : Pul rns :=
          match rns with
          | [::] => IH_UNil
          | rn :: rns' => IH_UCons rn (Fn rn) rns' (Ful rns')
          end
      in
      
      match rt with
      | LRTree rns => IH_LRTree rns (Fll rns)
      | URTree rns => IH_URTree rns (Ful rns)
      end.

  Definition ResponseTree_rec (P : forall l : L, ResponseTree l -> Set) := @ResponseTree_rect P.

  
  Definition ResponseTree_ind (P : forall l : L, ResponseTree l -> Prop)
             (Pn : ResponseNode -> Prop)
             (Pll : seq (B * ResponseNode) -> Prop)
             (Pul : seq ResponseNode -> Prop)
             (IH_LRTree : forall rns, Pll rns -> P Labeled (LRTree rns))
             (IH_URTree : forall rns, Pul rns -> P Unlabeled (URTree rns))
             (IH_Leaf : forall v, Pn (Leaf v))
             (IH_Object : forall rt, P Labeled rt -> Pn (Object rt))
             (IH_Array : forall rt, P Unlabeled rt -> Pn (Array rt))
             (IH_LNil : Pll [::])
             (IH_UNil : Pul [::])
             (IH_LCons : forall l rn, Pn rn -> forall rns, Pll rns -> Pll ((l, rn) :: rns))
             (IH_UCons : forall rn, Pn rn -> forall rns, Pul rns -> Pul (rn :: rns)) :=
    
    fix loop l rt : P l rt :=
      let fix Fn (rn : ResponseNode) : Pn rn :=
          match rn with
          | Leaf v => IH_Leaf v
          | Object rt => IH_Object rt (loop Labeled rt)
          | Array rt => IH_Array rt (loop Unlabeled rt)
          end
      in
      let fix Fll (rns : seq (B * ResponseNode)) : Pll rns :=
          match rns with
          | [::] => IH_LNil
          | (l, rn) :: rns' => IH_LCons l rn (Fn rn) rns' (Fll rns')
          end
      in
      let fix Ful (rns : seq ResponseNode) : Pul rns :=
          match rns with
          | [::] => IH_UNil
          | rn :: rns' => IH_UCons rn (Fn rn) rns' (Ful rns')
          end
      in
      
      match rt with
      | LRTree rns => IH_LRTree rns (Fll rns)
      | URTree rns => IH_URTree rns (Ful rns)
      end.
   *)

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
  
  (* Inductive Value : Type := *)
  (* | Null : Value *)
  (* | SingleValue : Vals -> Value. *)

  (* Definition option_of_value value := if value is SingleValue v then Some v else None. *)
  (* Definition value_of_option opt := if opt is Some v then SingleValue v else Null. *)

  (* Lemma option_of_valueK : cancel option_of_value value_of_option. *)
  (* Proof. *)
  (*     by case. *)
  (* Qed. *)

  (* Canonical value_eqType := EqType Value (CanEqMixin option_of_valueK). *)
  
  Definition GraphQLResponse := seq (Name * (@ResponseNode (option Vals))).

End GraphQLResponse.

Arguments ResponseNode [A].
Arguments Leaf [A].
Arguments Object [A].
Arguments Array [A].


Delimit Scope response_scope with RESP.
Open Scope response_scope.

Notation "{- ρ -}" := (Object ρ) : response_scope.
  
  