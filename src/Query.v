From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.



Section Query.


  Variables Name Vals : ordType.
  
  Inductive Query : Type :=
  | SingleField : Name -> {fmap Name -> Vals} -> Query
  | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
  | NestedField : Name -> {fmap Name -> Vals} -> Query -> Query
  | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> Query -> Query
  | InlineFragment : Name -> Query -> Query    (* Check it's named type and not list *)
  | SelectionSet : Query -> Query -> Query.   (* seq Query but not empty... *)


  Inductive ResponseObject : Type :=
  | Empty : ResponseObject
  | Null : Name -> ResponseObject
  | SingleResult : Name -> Vals -> ResponseObject
  | ListResult : Name -> list Vals -> ResponseObject
  | NestedResult : Name -> ResponseObject -> ResponseObject
  | NestedListResult : Name -> list ResponseObject -> ResponseObject
  | ResponseList : ResponseObject -> ResponseObject -> ResponseObject.



  (* Right now it is returning a GenTree.tree (Name * Name * {fmap Name -> Vals})
     
     The tuple represents (label, field name, args) but for the case of unlabeled fields
     there is some redundancy, where the label is the same as the field name.

     Another option would be to return a GenTree.tree ((Name, {fmap ...}) + (Name, Name, {fmap ...}))
     but this option doesn't allow (currently) to define Query as ordType, due to sum type
     not being of ordType itself.
   *)
    Fixpoint tree_of_query query : GenTree.tree (Name * Name * {fmap Name -> Vals})  :=
    match query with
    | SingleField name args => GenTree.Node 0 [:: GenTree.Leaf (name, name, args)]
    | LabeledField label name args => GenTree.Node 1 [:: GenTree.Leaf (label, name, args)]
    | NestedField name args ϕ => GenTree.Node 2 [:: GenTree.Leaf (name, name, args);
                                                  tree_of_query ϕ]
    | NestedLabeledField label name args ϕ =>  GenTree.Node 3 [:: GenTree.Leaf (label, name, args);
                                                                tree_of_query ϕ]
    | InlineFragment t ϕ => GenTree.Node 4 [:: GenTree.Leaf (t, t, emptym) ;
                                             tree_of_query ϕ]
    | SelectionSet ϕ ϕ' => GenTree.Node 5 [:: tree_of_query ϕ ; tree_of_query ϕ']
    end.

  Fixpoint query_of_tree (tree : GenTree.tree (Name * Name * {fmap Name -> Vals})) : option Query :=
    match tree with
    | GenTree.Node 0 [:: GenTree.Leaf (_, name, args)] => Some (SingleField name args)
    | GenTree.Node 1 [:: GenTree.Leaf (label, name, args)] => Some (LabeledField label name args)
    | GenTree.Node 2 [:: GenTree.Leaf (_, name, args); t'] =>
      if (query_of_tree t') is Some q then
        Some (NestedField name args q)
      else
        None
    | GenTree.Node 3 [:: GenTree.Leaf (label, name, args); t'] =>
      if (query_of_tree t') is Some q then
        Some (NestedLabeledField label name args q)
      else
        None
    |  GenTree.Node 4 [:: GenTree.Leaf (_, ty, emptym); t'] =>
       if (query_of_tree t') is Some q then
         Some (InlineFragment (NamedType ty) q)
       else
         None
    | GenTree.Node 5 [:: t' ; t''] =>
      match (query_of_tree t'), (query_of_tree t'') with
      | Some q, Some q' => Some (SelectionSet q q')
      | _, _ => None
      end
    | _ => None
    end.

  Lemma pcan_tree_of_query : pcancel tree_of_query query_of_tree.
  Proof.
    elim=> //.
      by move=> s args q /= ->.
      by move=> l s args q /= ->.
      by move=> t q /= ->.
      by move=> q H q' H' /=; rewrite H H'.
  Qed.

   Definition query_eqMixin := PcanEqMixin pcan_tree_of_query.
   Canonical query_eqType := EqType Query query_eqMixin.
   Definition query_choiceMixin := PcanChoiceMixin pcan_tree_of_query.
   Canonical query_choiceType := ChoiceType Query query_choiceMixin.
   Definition query_ordMixin := PcanOrdMixin pcan_tree_of_query.
   Canonical query_ordType := OrdType Query query_ordMixin.




   Fixpoint response_eq r1 r2 :=
     match r1, r2 with
     | Empty, Empty => true
     | Null l, Null l' => l == l'
     | SingleResult l val, SingleResult l' val' => (l == l') && (val == val')
     | ListResult l vals, ListResult l' vals' => (l == l') && (vals == vals')
     | NestedResult l r1', NestedResult l' r2' => (l == l') && (response_eq r1' r2')
     | NestedListResult l rs, NestedListResult l' rs' =>
       let fix loop s1 s2 :=
           match s1, s2 with
           | [::], [::] => true
           | r1 :: s1, r2 :: s2 => if response_eq r1 r2 then loop s1 s2 else false
           | _, _ => false
           end
       in
       (l == l') && loop rs rs'
     | ResponseList r1' r1'', ResponseList r2' r2'' => (response_eq r1' r2') && (response_eq r1'' r2'')
     | _, _ => false
     end.

     
   (*
   Fixpoint tree_of_response response : GenTree.tree (Name + (Vals + seq Vals)) :=
     match response with
     | Empty => GenTree.Node 0 [::]
     | Null l => GenTree.Node 1 [:: GenTree.Leaf (inl l)]
     | SingleResult l val => GenTree.Node 2 [:: GenTree.Leaf (inl l) ; GenTree.Leaf (inr (inl val))]
     | ListResult l vals => GenTree.Node 3 [:: GenTree.Leaf (inl l) ; GenTree.Leaf (inr (inr vals))]
     | NestedResult l q => GenTree.Node 4 [:: GenTree.Leaf (inl l) ; tree_of_response q]
     | NestedListResult l qs => GenTree.Node 5 (GenTree.Leaf (inl l) :: (map tree_of_response qs))
     | ResponseList q q' => GenTree.Node 6 [:: tree_of_response q ; tree_of_response q']
     end.


   Fixpoint response_of_tree (t : GenTree.tree (Name + (Vals + seq Vals))) :=
     match t with
     | GenTree.Node 0 [::] => Empty
     | GenTree.Node 1 [:: GenTree.Leaf (inl l)] => Null l
     | GenTree.Node 2 [:: GenTree.Leaf (inl l) ; GenTree.Leaf (inr (inl val))] => SingleResult l val
     | GenTree.Node 3 [:: GenTree.Leaf (inl l) ; GenTree.Leaf (inr (inr vals))] => ListResult l vals
     | GenTree.Node 4 [:: GenTree.Leaf (inl l) ; t'] => NestedResult l (response_of_tree t')
     | GenTree.Node 5 (GenTree.Leaf (inl l) :: t') => NestedListResult l (map response_of_tree t')
     | GenTree.Node 6 [::  t ; t'] => ResponseList (response_of_tree t) (response_of_tree t')
     | _ => Empty
     end.

   Lemma tree_of_responseK : cancel tree_of_response response_of_tree.
   Proof.
     elim=> //.
       by move=> s r /= ->.
       move=> s rs /=. rewrite map_nseq.
       
  Qed. *)
   
  (*
  Fixpoint query_eq q1 q2 :=
    match q1, q2 with
    | SingleField name args, SingleField name' args' => (name == name') && (args == args')
    | LabeledField label name args, LabeledField label' name' args' => (label == label') && (name == name') && (args == args')
    | NestedField name args ϕ, NestedField name' args' ϕ' => (name == name') && (args == args') && query_eq ϕ ϕ'
    | NestedLabeledField label name args ϕ, NestedLabeledField label' name' args' ϕ' =>
      (label == label') && (name == name') && (args == args') && query_eq ϕ ϕ'
    | InlineFragment t ϕ, InlineFragment t' ϕ' => (t == t') && query_eq ϕ ϕ'
    | SelectionSet ϕ ϕ', SelectionSet ψ ψ' => (query_eq ϕ ψ) &&  (query_eq ϕ' ψ')
    | _,  _ => false
    end.


  Lemma query_eqP : Equality.axiom query_eq.
  Proof.
    rewrite /Equality.axiom.
    move=> x y; apply: (iffP idP) => [| <- {y}].
    move: y; elim: x.
    by move=> n args; case=> n' args' //=; move/andP=> [/eqP -> /eqP ->].
    by move=> l n args; case=> l' n' args' //=; move/andP=> [/andP [/eqP -> /eqP ->] /eqP ->].
    move=> n args q IH; case=> // => n' args' q' /=; move/andP=> [/andP [/eqP -> /eqP ->] H].
      by apply IH in H; rewrite H.
    move=> l n args q IH; case=> // => l' n' args' q' /=; move/andP=> [/andP [/andP [/eqP -> /eqP ->] /eqP ->] H].
      by apply IH in H; rewrite H.
    move=> t q IH; case=> // => t' q' /=; move/andP=> [/eqP -> H].
      by apply IH in H; rewrite H.
    move=> q IH q' IH'. case=> // => q'' q''' //=. move/andP=> [H1 H2].
    by apply IH in H1; apply IH' in H2; rewrite H1 H2. 
    elim: x => /=.
    by move=> s f; rewrite !eqxx.
    by move=> l s f; rewrite !eqxx.
    by move=> s f q IH; rewrite !eqxx.
    by move=> l s f q IH; rewrite !eqxx.
    by move=> t q IH; rewrite !eqxx.
    move=> q IH q' IH'. rewrite !eqxx. *)
    
  Fixpoint isFieldSelection query :=
    match query with
    | SingleField _ _ => true
    | LabeledField _ _ _ => true
    | NestedField _ _ _ => true
    | NestedLabeledField _ _ _ _ => true
    | SelectionSet hd tl => isFieldSelection hd && isFieldSelection tl
    | _ => false
    end.

  Fixpoint isInlineFragmentSelection query :=
    match query with
    | InlineFragment _ _ => true
    | SelectionSet hd tl => isInlineFragmentSelection hd && isInlineFragmentSelection tl
    | _ => false
    end.
  
  Inductive GroundTypedNormalForm : Query -> Prop :=
  | GT_Field : forall f args,
      GroundTypedNormalForm (SingleField f args)

  | GT_LabeledField : forall label f args,
      GroundTypedNormalForm (LabeledField label f args)

  | GT_NestedField : forall f args ϕ,
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (NestedField f args ϕ)

  | GT_NestedLabeledField : forall label f args ϕ,
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (NestedLabeledField label f args ϕ)

  | GT_InlineFragment : forall t ϕ,
      (* isObjectType schema t *)
      isFieldSelection ϕ ->
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (InlineFragment t ϕ)

  | GT_SelectionSet : forall ϕ ϕ',
      (isFieldSelection ϕ && isFieldSelection ϕ') || (isInlineFragmentSelection ϕ && isInlineFragmentSelection ϕ') ->
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm ϕ' ->
      GroundTypedNormalForm (SelectionSet ϕ ϕ').

  Fixpoint is_ground_typed_normal_form query :=
    match query with
    | NestedField _ _ ϕ => is_ground_typed_normal_form ϕ
    | NestedLabeledField _ _ _ ϕ => is_ground_typed_normal_form ϕ
    | InlineFragment _ ϕ => isFieldSelection ϕ && is_ground_typed_normal_form ϕ
    | SelectionSet ϕ ϕ' => ((isFieldSelection ϕ && isFieldSelection ϕ')
                           || (isInlineFragmentSelection ϕ && isInlineFragmentSelection ϕ'))
                            && is_ground_typed_normal_form ϕ && is_ground_typed_normal_form ϕ'
    | _ => true
    end.
  
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].
Arguments SelectionSet [Name Vals].

Arguments Null [Name Vals].
Arguments Empty [Name Vals].