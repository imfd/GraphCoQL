From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord.


Require Import treeordtype.

Require Import SeqExtra.


Section Label.
(** Tag to discriminate between a tree with labels in its edges 
     or without them.  **)
  Inductive L :=
  | Labeled: L
  | Unlabeled : L.

  Derive NoConfusion for L.
End Label.


Section Response.

  Context {A B : eqType}.
  
  Unset Elimination Schemes.

  Inductive ResponseNode : Type :=
  | Leaf : A -> ResponseNode
  | Object : seq (B * ResponseNode) -> ResponseNode
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
  where lrsize (r : seq (B * ResponseNode)) : nat :=
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
  where are_non_redundant (responses : seq (B * ResponseNode)) : bool  :=
    {
      are_non_redundant [::] := true;

      are_non_redundant ((k, q) :: qs) := [&& is_non_redundant q,
                                          all (fun kq => kq.1 != k) qs &
                                          are_non_redundant qs]
    }.
  
  (*
  Fixpoint is_scalar {labeled} (rtree : ResponseTree labeled) : bool :=
    match rtree with
    | LRTree rns => all (fun r => r.2.(is_scalar_node)) rns
    | URTree rns => all is_scalar_node rns
    end
  with is_scalar_node (rnode : ResponseNode) : bool :=
         match rnode with
         | Leaf _ => true
         | Object _ => false
         | Array rt => is_scalar rt
         end.

  
  Definition response_labels {labeled} (rtree : ResponseTree labeled) : seq B :=
    match rtree with
    | LRTree rns => [seq rn.1 | rn <- rns]
    | _ => [::]
    end.

  Equations response_labels' (response : ResponseTree Labeled) : seq B :=
    {
      response_labels' (LRTree rns) := [seq rn.1 | rn <- rns]
    }.


  Fixpoint rtree_height {labeled} (rtree : ResponseTree labeled) : nat :=
     match rtree with
    | LRTree rns => seq_max [seq rnode_height rn.2 | rn <- rns]
    | URTree rns => seq_max [seq rnode_height rn | rn <- rns]
    end
  with rnode_height (rnode : ResponseNode) : nat :=
         match rnode with
         | Leaf _ => 0
         | Object rt => (rtree_height rt).+1
         | Array rt => (rtree_height rt).+1
         end.
   *)

  
  (*
  Equations rtree_depth {labeled} (rtree : ResponseTree labeled) : nat :=
    {
      rtree_depth (LRTree rns) := (max_lsize rns).+1;
      rtree_depth (URTree rns) := (max_usize rns).+1
    }
  where
  max_lsize (l : seq (B * ResponseNode)) : nat :=
    {
      max_lsize [::] := 0;
      max_lsize (rn :: rns) := max (rnode_depth rn.2) (max_lsize rns)
    }
  where
  max_usize (l : seq (ResponseNode)) : nat :=
    {
      max_usize [::] := 0;
      max_usize (rn :: rns) := max (rnode_depth rn) (max_usize rns)
    }
  where
  rnode_depth (rn : ResponseNode) : nat :=
    {
      rnode_depth (Leaf _) := 0;
      rnode_depth (Object rt) := (rtree_depth rt).+1;
      rnode_depth (Array rt) := (rtree_depth rt).+1
    }.
   *)
  
  (* 

  Equations list_of_ltree (response : ResponseTree Labeled) : seq (Name * ResponseNode) :=
    {
      list_of_ltree (LRTree rns) := rns
    }.
  
  Equations list_of_utree (response : ResponseTree Unlabeled) : seq ResponseNode :=
    {
      list_of_utree (URTree rns) := rns
    }.
  
  
  Equations list_of_tree {labeled : L} (response : ResponseTree labeled) : seq (Name * ResponseNode) + seq ResponseNode :=
    {
      list_of_tree (LRTree rns) := inl (list_of_ltree (LRTree rns));
      list_of_tree (URTree rns) := inr (list_of_utree (URTree rns))
    }.



  

  Equations rtree_cat {labeled} (rt1 rt2 : ResponseTree labeled) : ResponseTree labeled :=
    {
      rtree_cat (LRTree rns1) (LRTree rns2) := LRTree (rns1 ++ rns2);
      rtree_cat (URTree rns1) (URTree rns2) := URTree (rns1 ++ rns2)
    }.

  Lemma max_usize_cat rns1 rns2 : max_usize (rns1 ++ rns2) = max (max_usize rns1) (max_usize rns2).
  Proof.
    elim: rns1 rns2 => //= rn1 rns1 IH rns2.
    case: rn1; intros; [by simpl; apply: IH| |];
      by rewrite -Nat.max_assoc /= IH.
  Qed.

  Lemma max_lsize_cat rns1 rns2 : max_lsize (rns1 ++ rns2) = max (max_lsize rns1) (max_lsize rns2).
  Proof.
    elim: rns1 rns2 => //= rn1 rns1 IH rns2.
    case: rn1.2; intros; [by simpl; apply: IH| |];
      by rewrite -Nat.max_assoc /= IH.
  Qed.
  
  Lemma rtree_depth_cat l (rs1 rs2 : ResponseTree l) : rtree_depth (rtree_cat rs1 rs2) = max (rtree_depth rs1) (rtree_depth rs2).
  Proof.
    funelim (rtree_cat rs1 rs2) => /=; simp rtree_depth; congr S; [apply: max_lsize_cat | apply: max_usize_cat].
  Qed.



Section Map.
       
  Context {A B : Type} {Name : ordType} (f : A -> B).
  
  Equations map_rtree {labeled} (response : @ResponseTree A Name labeled) : @ResponseTree B Name labeled :=
    {
      map_rtree (LRTree rns) := LRTree (map_llist rns);
      map_rtree (URTree rns) := URTree (map_ulist rns)
      
    }
  where map_llist (l : seq (Name * @ResponseNode A Name)) : seq (Name * @ResponseNode B Name) :=
          {
            map_llist [::] := [::];
            map_llist ((l, rn) :: rns) := (l, map_node rn) :: map_llist rns
          }
  where map_ulist (l : seq (@ResponseNode A Name)) : seq (@ResponseNode B Name ) :=
          {
            map_ulist [::] := [::];
            map_ulist (rn :: rns) := (map_node rn) :: map_ulist rns
          }
  where map_node (rnode : @ResponseNode A Name) : @ResponseNode B Name :=
          {
            map_node (Leaf v) := Leaf (f v);
            map_node (Object rt) := Object (map_rtree rt);
            map_node (Array rt) := Array (map_rtree rt)
          }.

  Equations map_rtree_def {labeled} (response : @ResponseTree A Name labeled) : ResponseTree labeled :=
    {
      map_rtree_def (LRTree rns) := LRTree [seq (rn.1, map_node rn.2) | rn <- rns];
      map_rtree_def (URTree rns) := URTree [seq (map_node rn) | rn <- rns]      
    }.

  Lemma map_rtree_equation l (rt : ResponseTree l) : map_rtree rt = map_rtree_def rt.
  Proof.
    apply (map_rtree_elim
             (fun l rt res =>
                res = map_rtree_def rt)
             (fun l res =>
                res = [seq (rn.1, map_node rn.2) | rn <- l])
             (fun l res =>
                res = [seq (map_node rn) | rn <- l])
             (fun rn res =>
                res = map_node rn)) => //=.
    - elim=> // rn rns; simp map_rtree_def => IH; simp map_llist => /= H; by rewrite H.
    - by move=> label rn rns _ ->. 
  Qed.
*)
    
End Response.


Section GraphQLResponse.
  
  Context {Name Vals : ordType}.
  
  Inductive Value : Type :=
  | Null : Value
  | SingleValue : Vals -> Value.

   Definition option_of_value value := if value is SingleValue v then Some v else None.
  Definition value_of_option opt := if opt is Some v then SingleValue v else Null.

  Lemma option_of_valueK : cancel option_of_value value_of_option.
  Proof.
      by case.
  Qed.

  Canonical value_eqType := EqType Value (CanEqMixin option_of_valueK).
  
  Definition GraphQLResponse := seq (Name * (@ResponseNode value_eqType Name)).

End GraphQLResponse.

    (*
      
    Fixpoint all_scalar_or_object {labeled} (response : GraphQLResponse labeled) : bool :=
      match response with
      | LRTree rns => all (fun r => r.2.(is_scalar_node)) rns || all (fun r => r.2.(is_object)) rns
      | URTree rns => all is_scalar_node rns || all is_object rns
      end.
    
    Fixpoint valid_raw {labeled} (response : GraphQLResponse labeled) : bool :=
      match response with
      | LRTree rt => all (fun rn => valid_node rn.2) rt
      | URTree rt => all valid_node rt
      end
    with valid_node (rn : ResponseNode) : bool :=
           match rn with
           | Leaf v => true
           | Object rt => valid_raw rt
           | Array rt => (all_scalar_or_object rt) && valid_raw rt
           end.


    Structure raw_response {labeled : L} : Type :=
      RawResponse {
          rresponse :> GraphQLResponse labeled;
          _ : valid_raw rresponse
        }.

    
    End RawResponse.

End GraphQLResponse.
*)

(*
Section ListIn.
  
  Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
    map_In nil _ := nil;
    map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).
    
End ListIn.
 *)

  
  